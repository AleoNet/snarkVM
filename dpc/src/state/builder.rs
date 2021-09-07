// Copyright (C) 2019-2021 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

use crate::prelude::*;
use snarkvm_utilities::ToBytes;

use anyhow::{anyhow, Result};
use rand::{CryptoRng, Rng};
use std::sync::Arc;

#[derive(Clone)]
pub struct StateBuilder<C: Parameters> {
    /// A list of given inputs for a state transition.
    inputs: Vec<Input<C>>,
    /// A list of expected outputs for a state transition.
    outputs: Vec<Output<C>>,
    /// A publicly-visible field with data from the state transition.
    memo: Vec<u8>,
    /// A list of errors accumulated from calling the builder.
    errors: Vec<String>,
}

impl<C: Parameters> StateBuilder<C> {
    ///
    /// Initializes a new instance of `StateBuilder`.
    ///
    pub fn new() -> Self {
        Self {
            inputs: Vec::new(),
            outputs: Vec::new(),
            memo: Vec::new(),
            errors: Vec::new(),
        }
    }

    ///
    /// Adds the given input into the builder.
    ///
    pub fn add_input(mut self, input: Input<C>) -> Self {
        // Ensure there are no outputs assigned yet, as the builder computes joint serial numbers.
        if !self.outputs.is_empty() {
            self.errors.push("Builder cannot add new inputs after outputs".into());
        }

        match self.inputs.len() < C::NUM_INPUT_RECORDS {
            true => self.inputs.push(input),
            false => self.errors.push("Builder exceeded maximum inputs".into()),
        };
        self
    }

    ///
    /// Adds the given inputs into the builder.
    ///
    pub fn add_inputs(mut self, inputs: Vec<Input<C>>) -> Self {
        for input in inputs {
            self = self.add_input(input);
        }
        self
    }

    ///
    /// Adds the given output into the builder.
    ///
    pub fn add_output(mut self, output: Output<C>) -> Self {
        match self.outputs.len() < C::NUM_OUTPUT_RECORDS {
            true => self.outputs.push(output),
            false => self.errors.push("Builder exceeded maximum outputs".into()),
        };
        self
    }

    ///
    /// Adds the given outputs into the builder.
    ///
    pub fn add_outputs(mut self, outputs: Vec<Output<C>>) -> Self {
        for output in outputs {
            self = self.add_output(output);
        }
        self
    }

    ///
    /// Appends the given data to the memo field in the builder.
    ///
    pub fn append_memo(mut self, data: &Vec<u8>) -> Self {
        // TODO (howardwu): Change this to not be hardcoded to 64.
        match self.memo.len() < 64 && (self.memo.len() + data.len()) <= 64 {
            true => self.memo.extend_from_slice(data),
            false => self.errors.push("Builder exceeded maximum memo size".into()),
        };
        self
    }

    /// TODO (howardwu): TEMPORARY - `noop: Arc<NoopProgram<C>>` will be removed when `DPC::setup` and `DPC::load` are refactored.
    ///
    /// Finalizes the builder and returns a new instance of `State`.
    ///
    pub fn build<R: Rng + CryptoRng>(&mut self, noop: Arc<NoopProgram<C>>, rng: &mut R) -> Result<StateTransition<C>> {
        // Ensure there are no errors in the build process yet.
        if !self.errors.is_empty() {
            for error in &self.errors {
                eprintln!("{}", error);
            }
            return Err(anyhow!("State builder encountered build errors: {:?}", self.errors));
        }

        // Prepare the inputs and outputs for constructing state.
        let (inputs, outputs) = self.prepare_inputs_and_outputs(noop, rng)?;

        // Compute the input records.
        let input_records: Vec<_> = inputs
            .iter()
            .take(C::NUM_INPUT_RECORDS)
            .map(|input| input.record().clone())
            .collect();

        // Compute the serial numbers.
        let serial_numbers: Vec<_> = inputs
            .iter()
            .take(C::NUM_INPUT_RECORDS)
            .map(|input| input.serial_number().clone())
            .collect();

        // Compute the signature randomizers.
        let signature_randomizers: Vec<_> = inputs
            .iter()
            .take(C::NUM_INPUT_RECORDS)
            .map(|input| input.signature_randomizer().clone())
            .collect();

        // Compute the noop private keys.
        let noop_private_keys: Vec<_> = inputs
            .iter()
            .take(C::NUM_INPUT_RECORDS)
            .map(|input| input.noop_private_key().clone())
            .collect();

        // Compute an instance of the output records, commitments, and value balance.
        let (output_records, commitments, value_balance) = {
            // Compute the joint serial numbers.
            let mut joint_serial_numbers = Vec::with_capacity(C::NUM_INPUT_RECORDS);
            for serial_number in serial_numbers.iter().take(C::NUM_INPUT_RECORDS) {
                joint_serial_numbers.extend_from_slice(&serial_number.to_bytes_le()?);
            }

            // Compute the output records.
            let mut output_records = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);
            for (j, output) in outputs.iter().enumerate().take(C::NUM_OUTPUT_RECORDS) {
                let position = (C::NUM_INPUT_RECORDS + j) as u8;
                output_records.push(output.to_record(position, &joint_serial_numbers, rng)?);
            }

            // Compute the commitments.
            let commitments = output_records
                .iter()
                .take(C::NUM_OUTPUT_RECORDS)
                .map(|output| output.commitment())
                .collect();

            // Compute the value balance.
            let mut value_balance = AleoAmount::ZERO;
            for record in input_records.iter().take(C::NUM_INPUT_RECORDS) {
                value_balance = value_balance.add(AleoAmount::from_bytes(record.value() as i64));
            }
            for record in output_records.iter().take(C::NUM_OUTPUT_RECORDS) {
                value_balance = value_balance.sub(AleoAmount::from_bytes(record.value() as i64));
            }

            (output_records, commitments, value_balance)
        };

        // TODO (howardwu): Change this to not be hardcoded to 64.
        // Process the memo.
        let mut memo = [0u8; 64];
        self.memo.write_le(&mut memo[..])?;

        // Construct the transaction kernel.
        let kernel = TransactionKernel::new(serial_numbers, commitments, value_balance, memo)?;

        // Construct the executables.
        let executables: Vec<_> = inputs
            .iter()
            .map(|state| state.executable().clone())
            .chain(outputs.iter().map(|state| state.executable().clone()))
            .collect();

        // Update the builder with the new inputs and outputs, now that all operations have succeeded.
        self.inputs = inputs;
        self.outputs = outputs;

        Ok(StateTransition {
            kernel,
            input_records,
            output_records,
            signature_randomizers,
            noop_private_keys,
            executables,
        })
    }

    /// TODO (howardwu): TEMPORARY - `noop: Arc<NoopProgram<C>>` will be removed when `DPC::setup` and `DPC::load` are refactored.
    ///
    /// Prepares the inputs and outputs for the `Self::build()` phase.
    ///
    /// This method pads a copy of all inputs and outputs up to the requisite number
    /// of inputs and outputs for the transaction.
    ///
    fn prepare_inputs_and_outputs<R: Rng + CryptoRng>(
        &self,
        noop: Arc<NoopProgram<C>>,
        rng: &mut R,
    ) -> Result<(Vec<Input<C>>, Vec<Output<C>>)> {
        // Ensure a valid number of inputs are provided.
        if self.inputs.len() > C::NUM_INPUT_RECORDS {
            return Err(anyhow!("Builder exceeded maximum number of inputs"));
        }
        // Ensure a valid number of outputs are provided.
        if self.outputs.len() > C::NUM_OUTPUT_RECORDS {
            return Err(anyhow!("Builder exceeded maximum number of outputs"));
        }

        // Construct the inputs.
        let mut inputs = self.inputs.clone();
        // Pad the inputs with noop inputs if necessary.
        while inputs.len() < C::NUM_INPUT_RECORDS {
            // TODO (howardwu): Decide whether to "push" or "push_front" for program flow.
            inputs.push(Input::new_noop(noop.clone(), rng)?);
        }

        // Construct the outputs.
        let mut outputs = self.outputs.clone();
        // Pad the outputs with noop outputs if necessary.
        while outputs.len() < C::NUM_OUTPUT_RECORDS {
            // TODO (howardwu): Decide whether to "push" or "push_front" for program flow.
            outputs.push(Output::new_noop(noop.clone(), rng)?);
        }

        Ok((inputs, outputs))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testnet2::*;

    use rand::{thread_rng, SeedableRng};
    use rand_chacha::ChaChaRng;
    use std::ops::Deref;

    const ITERATIONS: usize = 100;

    #[test]
    fn test_add_noop_input() {
        let noop_program = NoopProgram::<Testnet2Parameters>::load().unwrap();
        let noop = Arc::new(noop_program.clone());

        for _ in 0..ITERATIONS {
            // Sample a random seed for the RNG.
            let seed: u64 = thread_rng().gen();

            // Generate the expected input state.
            let (expected_record, expected_serial_number, expected_signature_randomizer) = {
                let rng = &mut ChaChaRng::seed_from_u64(seed);

                let account = Account::new(rng).unwrap();
                let input_record = Record::new_noop_input(noop_program.program_id(), account.address, rng).unwrap();
                let (serial_number, signature_randomizer) =
                    input_record.to_serial_number(&account.compute_key()).unwrap();

                (input_record, serial_number, signature_randomizer)
            };

            // Generate the candidate input state.
            let (candidate_record, candidate_serial_number, candidate_signature_randomizer, candidate_executable) = {
                let rng = &mut ChaChaRng::seed_from_u64(seed);

                let mut builder = StateBuilder::new();
                builder = builder.add_input(Input::new_noop(noop.clone(), rng).unwrap());
                builder.build(noop.clone(), rng).unwrap();

                (
                    builder.inputs[0].record().clone(),
                    builder.inputs[0].serial_number().clone(),
                    builder.inputs[0].signature_randomizer().clone(),
                    builder.inputs[0].executable().clone(),
                )
            };

            assert_eq!(expected_record, candidate_record);
            assert_eq!(expected_serial_number, candidate_serial_number);
            assert_eq!(expected_signature_randomizer, candidate_signature_randomizer);
            assert!(candidate_executable.is_noop());
        }
    }

    #[test]
    fn test_add_noop_output() {
        let noop_program = NoopProgram::<Testnet2Parameters>::load().unwrap();
        let noop = Arc::new(noop_program.clone());

        for _ in 0..ITERATIONS {
            // Sample a random seed for the RNG.
            let seed: u64 = thread_rng().gen();

            // Generate the given inputs.
            let mut given_rng = ChaChaRng::seed_from_u64(seed);
            let (_given_inputs, given_joint_serial_numbers) = {
                let mut inputs = Vec::with_capacity(Testnet2Parameters::NUM_INPUT_RECORDS);
                let mut joint_serial_numbers = Vec::with_capacity(Testnet2Parameters::NUM_INPUT_RECORDS);
                for _ in 0..Testnet2Parameters::NUM_INPUT_RECORDS {
                    let input = Input::new_noop(noop.clone(), &mut given_rng).unwrap();
                    let serial_number = input.serial_number().to_bytes_le().unwrap();

                    inputs.push(input);
                    joint_serial_numbers.extend_from_slice(&serial_number);
                }
                (inputs, joint_serial_numbers)
            };

            // Checkpoint the RNG and clone it.
            let mut expected_rng = given_rng.clone();
            let mut candidate_rng = given_rng.clone();

            // Generate the expected output state.
            let expected_record = {
                let account = Account::new(&mut expected_rng).unwrap();
                Record::new_noop_output(
                    noop_program.deref(),
                    account.address,
                    Testnet2Parameters::NUM_INPUT_RECORDS as u8,
                    &given_joint_serial_numbers,
                    &mut expected_rng,
                )
                .unwrap()
            };

            // Generate the candidate output state.
            let (candidate_address, candidate_value, candidate_payload, candidate_executable) = {
                let mut builder = StateBuilder::new();
                builder = builder.add_output(Output::new_noop(noop.clone(), &mut candidate_rng).unwrap());
                builder.build(noop.clone(), &mut candidate_rng).unwrap();
                (
                    builder.outputs[0].address(),
                    builder.outputs[0].value(),
                    builder.outputs[0].payload().clone(),
                    builder.outputs[0].executable().clone(),
                )
            };

            assert_eq!(expected_record.owner(), candidate_address);
            assert_eq!(expected_record.value(), candidate_value.0 as u64);
            assert_eq!(expected_record.payload(), &candidate_payload);
            assert!(candidate_executable.is_noop());
        }
    }
}
