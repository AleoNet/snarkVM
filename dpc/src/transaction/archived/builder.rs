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
use once_cell::sync::OnceCell;
use rand::{CryptoRng, Rng};
use std::sync::Arc;

pub struct TransitionBuilder<N: Network> {
    // /// The request for a state transition.
    // request: OnceCell<Request<N>>,
    // /// The function for a state transition.
    // function: OnceCell<Arc<dyn Function<N>>>,
    /// A list of given inputs for a state transition.
    inputs: Vec<Input<N>>,
    /// A list of expected outputs for a state transition.
    outputs: Vec<Output<N>>,
    /// A publicly-visible field with data from the state transition.
    memo: Vec<u8>,
    /// A list of errors accumulated from calling the builder.
    errors: Vec<String>,
}

impl<N: Network> TransitionBuilder<N> {
    ///
    /// Initializes a new instance of `TransitionBuilder`.
    ///
    pub fn new() -> Self {
        Self {
            // request: OnceCell::new(),
            // function: OnceCell::new(),
            inputs: Vec::with_capacity(N::NUM_INPUT_RECORDS),
            outputs: Vec::with_capacity(N::NUM_OUTPUT_RECORDS),
            memo: Vec::with_capacity(N::MEMO_SIZE_IN_BYTES),
            errors: Vec::new(),
        }
    }

    // ///
    // /// Adds the given request into the builder.
    // ///
    // pub fn add_request(mut self, request: Request<N>) -> Self {
    //     // Ensure the function is not already set.
    //     if self.function.get().is_some() {
    //         self.errors
    //             .push("Builder cannot add new request after adding a function".into());
    //     }
    //
    //     // // Ensure there are no outputs assigned yet.
    //     // if !self.outputs.is_empty() {
    //     //     self.errors
    //     //         .push("Builder cannot add a new request after outputs".into());
    //     // }
    //
    //     // Set the request.
    //     if self.request.get().is_some() {
    //         self.errors.push("Builder already set a request".into());
    //     } else if self.request.set(request).is_err() {
    //         self.errors.push("Builder failed to set a request".into());
    //     }
    //     self
    // }

    // ///
    // /// Adds the given function into the builder.
    // ///
    // pub fn add_function(mut self, function: Arc<dyn Function<N>>) -> Self {
    //     // // Ensure the request is already set and that the function ID matches in the request.
    //     // match self.request.get() {
    //     //     Some(request) => {
    //     //         if request.function_id() != function.function_id() {
    //     //             self.errors.push("Builder found a mismatch in the function ID".into())
    //     //         }
    //     //     }
    //     //     None => self
    //     //         .errors
    //     //         .push("Builder cannot add new function before adding a request".into()),
    //     // };
    //
    //     // Ensure there are no outputs assigned yet.
    //     if !self.outputs.is_empty() {
    //         self.errors
    //             .push("Builder cannot add a new function after outputs".into());
    //     }
    //
    //     // Set the function.
    //     if self.function.get().is_some() {
    //         self.errors.push("Builder already set a function".into());
    //     } else if self.function.set(function).is_err() {
    //         self.errors.push("Builder failed to set a function".into());
    //     }
    //     self
    // }

    ///
    /// Adds the given input into the builder.
    ///
    pub fn add_input(mut self, input: Input<N>) -> Self {
        // // Ensure the function is not already set.
        // if self.function.get().is_some() {
        //     self.errors
        //         .push("Builder cannot add new input after adding a function".into());
        // }

        // Ensure there are no outputs assigned yet.
        if !self.outputs.is_empty() {
            self.errors
                .push("Builder cannot add a new request after outputs".into());
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
        // Ensure the function is already set, or the output is a noop.
        if self.function.get().is_none() && !output.is_noop() {
            self.errors
                .push("Builder cannot add new outputs before adding a function".into());
        }

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

    // ///
    // /// Finalizes the builder and returns a new instance of `State`.
    // ///
    // pub fn build<R: Rng + CryptoRng>(&mut self, ledger_proof: LedgerProof<N>, rng: &mut R) -> Result<Transaction<N>> {
    //     // Ensure there are no errors in the build process yet.
    //     if !self.errors.is_empty() {
    //         for error in &self.errors {
    //             eprintln!("{}", error);
    //         }
    //         return Err(anyhow!(
    //             "Transition builder encountered build errors: {:?}",
    //             self.errors
    //         ));
    //     }
    //
    //     // // Fetch the request.
    //     // let request = match self.request.get() {
    //     //     Some(request) => request.clone(),
    //     //     None => return Err(anyhow!("Failed to get the request during build phase")),
    //     // };
    //     //
    //     // // Fetch the function.
    //     // let function = match self.function.get() {
    //     //     Some(function) => function.clone(),
    //     //     None => return Err(anyhow!("Failed to get the function during build phase")),
    //     // };
    //     //
    //     // let response = function.evaluate(&request)?;
    //     // let commitments = response.to_commitments().clone();
    //     // let ciphertexts = response.ciphertexts().clone();
    //
    //     // Prepare the inputs and outputs for constructing state.
    //     let (inputs, outputs) = self.prepare_inputs_and_outputs(rng)?;
    //
    //     // Compute the input records.
    //     let input_records: Vec<_> = inputs
    //         .iter()
    //         .take(N::NUM_INPUT_RECORDS)
    //         .map(|input| input.record().clone())
    //         .collect();
    //
    //     // Compute the serial numbers.
    //     let serial_numbers: Vec<_> = inputs
    //         .iter()
    //         .take(N::NUM_INPUT_RECORDS)
    //         .map(|input| input.serial_number().clone())
    //         .collect();
    //
    //     // Compute the output records.
    //     let output_records = outputs
    //         .iter()
    //         .enumerate()
    //         .take(N::NUM_OUTPUT_RECORDS)
    //         .map(|(i, output)| Ok(output.to_record(serial_numbers[i], rng)?))
    //         .collect::<Result<Vec<_>>>()?;
    //
    //     // Compute the commitments.
    //     let commitments = output_records
    //         .iter()
    //         .take(N::NUM_OUTPUT_RECORDS)
    //         .map(|output| output.commitment())
    //         .collect();
    //
    //     // Compute the value balance.
    //     let mut value_balance = AleoAmount::ZERO;
    //     for record in input_records.iter().take(N::NUM_INPUT_RECORDS) {
    //         value_balance = value_balance.add(AleoAmount::from_bytes(record.value() as i64));
    //     }
    //     for record in output_records.iter().take(N::NUM_OUTPUT_RECORDS) {
    //         value_balance = value_balance.sub(AleoAmount::from_bytes(record.value() as i64));
    //     }
    //
    //     // Construct the transition.
    //     let transition = Transition::<N>::from(serial_numbers, commitments, ciphertexts, value_balance)?;
    //     let transaction_id = transition.to_transition_id()?;
    //
    //     // Execute the program circuit.
    //     let execution_proof = function.execute(PublicVariables::new(transaction_id))?;
    //
    //
    //     //
    //     // // Ensure the executable input and output size requirements matches the records.
    //     // {
    //     //     // Fetch the function type and program ID.
    //     //     let (function_type, program_id) = (function.function_type(), function.program_id());
    //     //
    //     //     // Ensure the input records have the correct program ID.
    //     //     for i in 0..(function_type.input_count() as usize) {
    //     //         if input_records[i].program_id() != program_id {
    //     //             return Err(anyhow!("Program ID in input record {} does not match executable", i));
    //     //         }
    //     //     }
    //     //
    //     //     // Ensure the output records have the correct program ID.
    //     //     for j in 0..(function_type.output_count() as usize) {
    //     //         if output_records[j].program_id() != program_id {
    //     //             return Err(anyhow!("Program ID in output record {} does not match executable", j));
    //     //         }
    //     //     }
    //     // }
    //
    //     // // Compute the value balance.
    //     // let mut value_balance = AleoAmount::ZERO;
    //     // for record in input_records.iter().take(N::NUM_INPUT_RECORDS) {
    //     //     value_balance = value_balance.add(AleoAmount::from_bytes(record.value() as i64));
    //     // }
    //     // for record in output_records.iter().take(N::NUM_OUTPUT_RECORDS) {
    //     //     value_balance = value_balance.sub(AleoAmount::from_bytes(record.value() as i64));
    //     // }
    //     //
    //     // // Process the memo.
    //     // let mut memo_bytes = self.memo.clone();
    //     // match memo_bytes.len() > N::MEMO_SIZE_IN_BYTES {
    //     //     true => return Err(anyhow!("Memo size of {} exceeds capacity", memo_bytes.len())),
    //     //     false => memo_bytes.resize(N::MEMO_SIZE_IN_BYTES, 0u8),
    //     // };
    //     // let memo = Memo::new(&memo_bytes)?;
    //     //
    //     // // Compute the encrypted records.
    //     // let (ciphertexts, ciphertext_randomizers) = Self::encrypt_records(&output_records, rng)?;
    //     //
    //     // // Construct the transition.
    //     // let transition = Transition::<N>::new(serial_numbers, commitments, ciphertexts, value_balance)?;
    //     //
    //     // // Update the builder with the new inputs and outputs, now that all operations have succeeded.
    //     // self.outputs = outputs;
    //     //
    //     // Ok(State {
    //     //     transition,
    //     //     signatures,
    //     //     function,
    //     //     input_records,
    //     //     output_records,
    //     //     ciphertext_randomizers,
    //     //     memo,
    //     // })
    // }
    //
    // ///
    // /// Prepares the inputs and outputs for the `Self::build()` phase.
    // ///
    // /// This method pads a copy of all inputs and outputs up to the requisite number
    // /// of inputs and outputs for the transaction.
    // ///
    // fn prepare_inputs_and_outputs<R: Rng + CryptoRng>(&self, rng: &mut R) -> Result<(Vec<Input<N>>, Vec<Output<N>>)> {
    //     // // Set the executable with the noop if necessary.
    //     // if self.executable.get().is_none() {
    //     //     if self.executable.set(Executable::Noop).is_err() {
    //     //         return Err(anyhow!("Builder failed to set the noop executable"));
    //     //     }
    //     // }
    //
    //     // Ensure a valid number of inputs are provided.
    //     if self.inputs.len() > N::NUM_INPUT_RECORDS {
    //         return Err(anyhow!("Builder exceeded maximum number of inputs"));
    //     }
    //     // Ensure a valid number of outputs are provided.
    //     if self.outputs.len() > N::NUM_OUTPUT_RECORDS {
    //         return Err(anyhow!("Builder exceeded maximum number of outputs"));
    //     }
    //
    //     // Construct the inputs.
    //     let mut inputs = self.inputs.clone();
    //     // Pad the inputs with noop inputs if necessary.
    //     while inputs.len() < N::NUM_INPUT_RECORDS {
    //         inputs.push(Input::new_noop(rng)?);
    //     }
    //
    //     // Construct the outputs.
    //     let mut outputs = self.outputs.clone();
    //     // Pad the outputs with noop outputs if necessary.
    //     while outputs.len() < N::NUM_OUTPUT_RECORDS {
    //         outputs.push(Output::new_noop(rng)?);
    //     }
    //
    //     Ok((inputs, outputs))
    // }
}
//
// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::testnet2::*;
//
//     use rand::{thread_rng, SeedableRng};
//     use rand_chacha::ChaChaRng;
//
//     const ITERATIONS: usize = 100;
//
//     #[test]
//     fn test_add_noop_input() {
//         for _ in 0..ITERATIONS {
//             // Sample a random seed for the RNG.
//             let seed: u64 = thread_rng().gen();
//
//             // Generate the expected input state.
//             let (expected_record, expected_serial_number, expected_program_id) = {
//                 let rng = &mut ChaChaRng::seed_from_u64(seed);
//
//                 let account = Account::new(rng).unwrap();
//                 let input_record = Record::new_noop_input(account.address, rng).unwrap();
//                 let serial_number = input_record
//                     .to_serial_number(&account.private_key().to_compute_key().unwrap())
//                     .unwrap();
//                 let program_id = input_record.program_id();
//
//                 (input_record, serial_number, program_id)
//             };
//
//             // Generate the candidate input state.
//             let (candidate_record, candidate_serial_number, candidate_program_id) = {
//                 let rng = &mut ChaChaRng::seed_from_u64(seed);
//
//                 let mut builder = TransitionBuilder::<Testnet2>::new();
//                 builder = builder.add_input(Input::new_noop(rng).unwrap());
//                 builder.build(rng).unwrap();
//
//                 (
//                     builder.inputs[0].record().clone(),
//                     builder.inputs[0].serial_number().clone(),
//                     builder.inputs[0].program_id().clone(),
//                 )
//             };
//
//             assert_eq!(expected_record, candidate_record);
//             assert_eq!(expected_serial_number, candidate_serial_number);
//             assert_eq!(expected_program_id, candidate_program_id);
//         }
//     }
//
//     #[test]
//     fn test_add_noop_output() {
//         for _ in 0..ITERATIONS {
//             // Sample a random seed for the RNG.
//             let seed: u64 = thread_rng().gen();
//
//             // Generate the given inputs.
//             let mut given_rng = ChaChaRng::seed_from_u64(seed);
//             let (_given_inputs, given_serial_numbers) = {
//                 let mut inputs = Vec::with_capacity(Testnet2::NUM_INPUT_RECORDS);
//                 let mut serial_numbers = Vec::with_capacity(Testnet2::NUM_INPUT_RECORDS);
//                 for _ in 0..Testnet2::NUM_INPUT_RECORDS {
//                     let input = Input::<Testnet2>::new_noop(&mut given_rng).unwrap();
//                     let serial_number = input.serial_number().clone();
//
//                     inputs.push(input);
//                     serial_numbers.push(serial_number);
//                 }
//                 (inputs, serial_numbers)
//             };
//
//             // Checkpoint the RNG and clone it.
//             let mut expected_rng = given_rng.clone();
//             let mut candidate_rng = given_rng.clone();
//
//             // Generate the expected output state.
//             let expected_record = {
//                 let account = Account::<Testnet2>::new(&mut expected_rng).unwrap();
//                 Record::new_noop_output(account.address, given_serial_numbers[0], &mut expected_rng).unwrap()
//             };
//
//             // Generate the candidate output state.
//             let (candidate_address, candidate_value, candidate_payload, candidate_program_id) = {
//                 let mut builder = TransitionBuilder::new();
//                 builder = builder.add_output(Output::new_noop(&mut candidate_rng).unwrap());
//                 builder.build(&mut candidate_rng).unwrap();
//                 (
//                     builder.outputs[0].address(),
//                     builder.outputs[0].value(),
//                     builder.outputs[0].payload().clone(),
//                     builder.outputs[0].program_id(),
//                 )
//             };
//
//             assert_eq!(expected_record.owner(), candidate_address);
//             assert_eq!(expected_record.value(), candidate_value.0 as u64);
//             assert_eq!(expected_record.payload(), &candidate_payload);
//             assert_eq!(expected_record.program_id(), candidate_program_id);
//         }
//     }
// }
