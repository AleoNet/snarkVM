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

use anyhow::{anyhow, Result};
use rand::{CryptoRng, Rng};

#[derive(Clone)]
pub struct StateBuilder<N: Network> {
    /// A list of executables for a state transition.
    executables: Vec<Executable<N>>,
    /// A list of given inputs for a state transition.
    inputs: Vec<Input<N>>,
    /// A list of expected outputs for a state transition.
    outputs: Vec<Output<N>>,
    /// A publicly-visible field with data from the state transition.
    memo: Vec<u8>,
    /// A list of errors accumulated from calling the builder.
    errors: Vec<String>,
}

impl<N: Network> StateBuilder<N> {
    ///
    /// Initializes a new instance of `StateBuilder`.
    ///
    pub fn new() -> Self {
        Self {
            executables: Vec::with_capacity(N::NUM_EXECUTABLES),
            inputs: Vec::with_capacity(N::NUM_INPUT_RECORDS),
            outputs: Vec::with_capacity(N::NUM_OUTPUT_RECORDS),
            memo: Vec::with_capacity(N::MEMO_SIZE_IN_BYTES),
            errors: Vec::new(),
        }
    }

    ///
    /// Adds the given executable into the builder.
    ///
    pub fn add_executable(mut self, executable: Executable<N>) -> Self {
        match self.executables.len() < N::NUM_EXECUTABLES {
            true => self.executables.push(executable),
            false => self.errors.push("Builder exceeded maximum executables".into()),
        };
        self
    }

    ///
    /// Adds the given input into the builder.
    ///
    pub fn add_input(mut self, input: Input<N>) -> Self {
        // Ensure there are no outputs assigned yet, as the builder computes joint serial numbers.
        if !self.outputs.is_empty() {
            self.errors.push("Builder cannot add new inputs after outputs".into());
        }

        match self.inputs.len() < N::NUM_INPUT_RECORDS {
            true => self.inputs.push(input),
            false => self.errors.push("Builder exceeded maximum inputs".into()),
        };
        self
    }

    ///
    /// Adds the given inputs into the builder.
    ///
    pub fn add_inputs(mut self, inputs: Vec<Input<N>>) -> Self {
        for input in inputs {
            self = self.add_input(input);
        }
        self
    }

    ///
    /// Adds the given output into the builder.
    ///
    pub fn add_output(mut self, output: Output<N>) -> Self {
        match self.outputs.len() < N::NUM_OUTPUT_RECORDS {
            true => self.outputs.push(output),
            false => self.errors.push("Builder exceeded maximum outputs".into()),
        };
        self
    }

    ///
    /// Adds the given outputs into the builder.
    ///
    pub fn add_outputs(mut self, outputs: Vec<Output<N>>) -> Self {
        for output in outputs {
            self = self.add_output(output);
        }
        self
    }

    ///
    /// Appends the given data to the memo field in the builder.
    ///
    pub fn append_memo(mut self, data: &Vec<u8>) -> Self {
        match self.memo.len() < N::MEMO_SIZE_IN_BYTES && (self.memo.len() + data.len()) <= N::MEMO_SIZE_IN_BYTES {
            true => self.memo.extend_from_slice(data),
            false => self.errors.push("Builder exceeded maximum memo size".into()),
        };
        self
    }

    ///
    /// Finalizes the builder and returns a new instance of `State`.
    ///
    pub fn build<R: Rng + CryptoRng>(&mut self, rng: &mut R) -> Result<StateTransition<N>> {
        // Ensure there are no errors in the build process yet.
        if !self.errors.is_empty() {
            for error in &self.errors {
                eprintln!("{}", error);
            }
            return Err(anyhow!("State builder encountered build errors: {:?}", self.errors));
        }

        // Prepare the inputs and outputs for constructing state.
        let (inputs, outputs) = self.prepare_inputs_and_outputs(rng)?;

        // Compute the input records.
        let input_records: Vec<_> = inputs
            .iter()
            .take(N::NUM_INPUT_RECORDS)
            .map(|input| input.record().clone())
            .collect();

        // Compute the serial numbers.
        let serial_numbers: Vec<_> = inputs
            .iter()
            .take(N::NUM_INPUT_RECORDS)
            .map(|input| input.serial_number().clone())
            .collect();

        // Compute the noop private keys.
        let noop_private_keys: Vec<_> = inputs
            .iter()
            .take(N::NUM_INPUT_RECORDS)
            .map(|input| input.noop_private_key().clone())
            .collect();

        // Compute the output records.
        let output_records = outputs
            .iter()
            .enumerate()
            .take(N::NUM_OUTPUT_RECORDS)
            .map(|(i, output)| Ok(output.to_record(serial_numbers[i], rng)?))
            .collect::<Result<Vec<_>>>()?;

        // Compute the commitments.
        let commitments = output_records
            .iter()
            .take(N::NUM_OUTPUT_RECORDS)
            .map(|output| output.commitment())
            .collect();

        // Compute the value balance.
        let mut value_balance = AleoAmount::ZERO;
        for record in input_records.iter().take(N::NUM_INPUT_RECORDS) {
            value_balance = value_balance.add(AleoAmount::from_bytes(record.value() as i64));
        }
        for record in output_records.iter().take(N::NUM_OUTPUT_RECORDS) {
            value_balance = value_balance.sub(AleoAmount::from_bytes(record.value() as i64));
        }

        // Process the memo.
        let mut memo_bytes = self.memo.clone();
        match memo_bytes.len() > N::MEMO_SIZE_IN_BYTES {
            true => return Err(anyhow!("Memo size of {} exceeds capacity", memo_bytes.len())),
            false => memo_bytes.resize(N::MEMO_SIZE_IN_BYTES, 0u8),
        };
        let memo = Memo::new(&memo_bytes)?;

        // Construct the transaction kernel.
        let kernel = TransactionKernel::new(serial_numbers, commitments, value_balance, memo)?;

        // Construct the executables.
        let executables = Executables::from(self.executables.clone())?;
        if !executables.verify_records(&input_records, &output_records) {
            return Err(anyhow!("Program IDs in records do not match executables"));
        }

        // Update the builder with the new inputs and outputs, now that all operations have succeeded.
        self.inputs = inputs;
        self.outputs = outputs;

        Ok(StateTransition {
            kernel,
            input_records,
            output_records,
            noop_private_keys,
            // TODO (howardwu): TEMPORARY - Clean this up after usage is stabilized.
            executables: (*executables).clone(),
        })
    }

    //
    // fn is_compatible(&self) -> bool {
    //     // if !self.is_valid() {
    //     //     eprintln!("Executables is not well-formed");
    //     //     return false;
    //     // }
    //
    //     let mut num_inputs: usize = 0;
    //     let mut num_outputs: usize = 0;
    //
    //     for executable in &self.executables {
    //         // Fetch the program ID, input count, and output count.
    //         let (program_id, input_count, output_count) = match executable.circuit_type() {
    //             Ok(circuit_type) => {
    //                 let program_id = executable.program_id();
    //                 let input_count = circuit_type.input_count() as usize;
    //                 let output_count = circuit_type.output_count() as usize;
    //                 (program_id, input_count, output_count)
    //             }
    //             Err(error) => {
    //                 eprintln!("{}", error);
    //                 return false;
    //             }
    //         };
    //
    //         // Verify the input records have the correct program ID.
    //         for i in 0..input_count {
    //             if self.input_records[num_inputs + i].program_id() != program_id {
    //                 eprintln!("Program ID in input record {} does not match executable", i);
    //                 return false;
    //             }
    //         }
    //
    //         // Verify the output records have the correct program ID.
    //         for j in 0..output_count {
    //             if self.output_records[num_outputs + j].program_id() != program_id {
    //                 eprintln!("Program ID in output record {} does not match executable", j);
    //                 return false;
    //             }
    //         }
    //
    //         // Increment the number of inputs and outputs from this executable.
    //         num_inputs += input_count;
    //         num_outputs += output_count;
    //     }
    //
    //     true
    // }
    //

    ///
    /// Prepares the inputs and outputs for the `Self::build()` phase.
    ///
    /// This method pads a copy of all inputs and outputs up to the requisite number
    /// of inputs and outputs for the transaction.
    ///
    fn prepare_inputs_and_outputs<R: Rng + CryptoRng>(&self, rng: &mut R) -> Result<(Vec<Input<N>>, Vec<Output<N>>)> {
        // Ensure a valid number of inputs are provided.
        if self.inputs.len() > N::NUM_INPUT_RECORDS {
            return Err(anyhow!("Builder exceeded maximum number of inputs"));
        }
        // Ensure a valid number of outputs are provided.
        if self.outputs.len() > N::NUM_OUTPUT_RECORDS {
            return Err(anyhow!("Builder exceeded maximum number of outputs"));
        }

        // Construct the inputs.
        let mut inputs = self.inputs.clone();
        // Pad the inputs with noop inputs if necessary.
        while inputs.len() < N::NUM_INPUT_RECORDS {
            inputs.push(Input::new_noop(rng)?);
        }

        // Construct the outputs.
        let mut outputs = self.outputs.clone();
        // Pad the outputs with noop outputs if necessary.
        while outputs.len() < N::NUM_OUTPUT_RECORDS {
            outputs.push(Output::new_noop(rng)?);
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

    const ITERATIONS: usize = 100;

    #[test]
    fn test_add_noop_input() {
        for _ in 0..ITERATIONS {
            // Sample a random seed for the RNG.
            let seed: u64 = thread_rng().gen();

            // Generate the expected input state.
            let (expected_record, expected_serial_number, expected_program_id) = {
                let rng = &mut ChaChaRng::seed_from_u64(seed);

                let account = Account::new(rng).unwrap();
                let input_record = Record::new_noop_input(account.address, rng).unwrap();
                let serial_number = input_record
                    .to_serial_number(&account.private_key().to_compute_key().unwrap())
                    .unwrap();
                let program_id = input_record.program_id();

                (input_record, serial_number, program_id)
            };

            // Generate the candidate input state.
            let (candidate_record, candidate_serial_number, candidate_program_id) = {
                let rng = &mut ChaChaRng::seed_from_u64(seed);

                let mut builder = StateBuilder::<Testnet2>::new();
                builder = builder.add_input(Input::new_noop(rng).unwrap());
                builder.build(rng).unwrap();

                (
                    builder.inputs[0].record().clone(),
                    builder.inputs[0].serial_number().clone(),
                    builder.inputs[0].program_id().clone(),
                )
            };

            assert_eq!(expected_record, candidate_record);
            assert_eq!(expected_serial_number, candidate_serial_number);
            assert_eq!(expected_program_id, candidate_program_id);
        }
    }

    #[test]
    fn test_add_noop_output() {
        for _ in 0..ITERATIONS {
            // Sample a random seed for the RNG.
            let seed: u64 = thread_rng().gen();

            // Generate the given inputs.
            let mut given_rng = ChaChaRng::seed_from_u64(seed);
            let (_given_inputs, given_serial_numbers) = {
                let mut inputs = Vec::with_capacity(Testnet2::NUM_INPUT_RECORDS);
                let mut serial_numbers = Vec::with_capacity(Testnet2::NUM_INPUT_RECORDS);
                for _ in 0..Testnet2::NUM_INPUT_RECORDS {
                    let input = Input::<Testnet2>::new_noop(&mut given_rng).unwrap();
                    let serial_number = input.serial_number().clone();

                    inputs.push(input);
                    serial_numbers.push(serial_number);
                }
                (inputs, serial_numbers)
            };

            // Checkpoint the RNG and clone it.
            let mut expected_rng = given_rng.clone();
            let mut candidate_rng = given_rng.clone();

            // Generate the expected output state.
            let expected_record = {
                let account = Account::<Testnet2>::new(&mut expected_rng).unwrap();
                Record::new_noop_output(account.address, given_serial_numbers[0], &mut expected_rng).unwrap()
            };

            // Generate the candidate output state.
            let (candidate_address, candidate_value, candidate_payload, candidate_program_id) = {
                let mut builder = StateBuilder::new();
                builder = builder.add_output(Output::new_noop(&mut candidate_rng).unwrap());
                builder.build(&mut candidate_rng).unwrap();
                (
                    builder.outputs[0].address(),
                    builder.outputs[0].value(),
                    builder.outputs[0].payload().clone(),
                    builder.outputs[0].program_id(),
                )
            };

            assert_eq!(expected_record.owner(), candidate_address);
            assert_eq!(expected_record.value(), candidate_value.0 as u64);
            assert_eq!(expected_record.payload(), &candidate_payload);
            assert_eq!(expected_record.program_id(), candidate_program_id);
        }
    }
}
