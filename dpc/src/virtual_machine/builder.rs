// Copyright (C) 2019-2022 Aleo Systems Inc.
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
use snarkvm_algorithms::CommitmentScheme;
use snarkvm_utilities::{ToBytes, Uniform};

use anyhow::{anyhow, Result};
use once_cell::sync::OnceCell;
use rand::{CryptoRng, Rng};

#[derive(Clone)]
pub struct ResponseBuilder<N: Network> {
    /// The request for a state transition.
    request: OnceCell<Request<N>>,
    /// A list of expected outputs for a state transition.
    outputs: Vec<Output<N>>,
    /// A publicly-visible field encoding events from the state transition.
    events: Vec<Event<N>>,
    /// A list of errors accumulated from calling the builder.
    errors: Vec<String>,
}

impl<N: Network> ResponseBuilder<N> {
    ///
    /// Initializes a new instance of `ResponseBuilder`.
    ///
    pub fn new() -> Self {
        Self {
            request: OnceCell::new(),
            outputs: Vec::with_capacity(N::NUM_OUTPUTS as usize),
            events: Vec::with_capacity(N::NUM_EVENTS as usize),
            errors: Vec::with_capacity(N::NUM_TRANSITIONS as usize),
        }
    }

    ///
    /// Adds the given request into the builder.
    ///
    pub fn add_request(mut self, request: Request<N>) -> Self {
        if self.request.get().is_some() {
            self.errors.push("Builder already set a request".into());
        } else if self.request.set(request).is_err() {
            self.errors.push("Builder failed to set a request".into());
        }
        self
    }

    ///
    /// Adds the given output into the builder.
    ///
    pub fn add_output(mut self, output: Output<N>) -> Self {
        // Ensure the request is already set, or the output is a noop.
        if self.request.get().is_none() && !output.is_noop() {
            self.errors.push("Builder cannot add new outputs before adding a request".into());
        }

        match self.outputs.len() < N::NUM_OUTPUTS as usize {
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
    /// Adds the given event into the builder.
    ///
    pub fn add_event(mut self, event: Event<N>) -> Self {
        match self.events.len() < N::NUM_EVENTS as usize {
            true => self.events.push(event),
            false => self.errors.push("Builder exceeded maximum number of events".into()),
        };
        self
    }

    ///
    /// Finalizes the builder and returns a new instance of `Response`.
    ///
    pub fn build<R: Rng + CryptoRng>(&self, rng: &mut R) -> Result<Response<N>> {
        // Ensure there are no errors in the build process yet.
        if !self.errors.is_empty() {
            for error in &self.errors {
                eprintln!("{}", error);
            }
            return Err(anyhow!("State builder encountered build errors: {:?}", self.errors));
        }

        // Fetch the request.
        let request = match self.request.get() {
            Some(request) => request,
            None => return Err(anyhow!("Builder is missing request")),
        };

        // Fetch the events.
        let mut events = self.events.clone();

        // Construct the state.
        let program_id = request.to_program_id()?;

        // Construct the inputs.
        let input_records = request.records();
        let serial_numbers = request.to_serial_numbers()?;

        // Compute the output records.
        let (output_records, encryption_randomness): (Vec<_>, Vec<_>) = self
            .outputs
            .iter()
            .enumerate()
            .take(N::NUM_OUTPUTS as usize)
            .map(|(i, output)| {
                let (record, encryption_randomness) = output.to_record(rng)?;

                // Add the record view key event if the output record is public.
                if request.is_public() && events.len() < N::NUM_EVENTS as usize {
                    events.push(Event::RecordViewKey(i as u8, record.record_view_key().clone()))
                }

                Ok((record, encryption_randomness))
            })
            .collect::<Result<Vec<_>>>()?
            .into_iter()
            .unzip();

        // Ensure the input records have the correct program ID.
        for (i, input_record) in input_records.iter().enumerate().take(N::NUM_INPUTS as usize) {
            if input_record.program_id() != program_id {
                return Err(anyhow!("Program ID in input record {} is incorrect", i));
            }
        }

        // TODO (raychu86): Check this. Currently blocking program deployments.
        // // Ensure the output records have the correct program ID.
        // for j in 0..(function_type.output_count() as usize) {
        //     if output_records[j].program_id() != program_id {
        //         return Err(anyhow!("Program ID in output record {} is incorrect", j));
        //     }
        // }

        // Compute the commitments.
        let commitments: Vec<_> = output_records.iter().take(N::NUM_OUTPUTS as usize).map(Record::commitment).collect();

        // Compute the value balance.
        let mut value_balance = AleoAmount::ZERO;
        for record in input_records.iter().take(N::NUM_INPUTS as usize) {
            value_balance = value_balance.add(record.value());
        }
        for record in output_records.iter().take(N::NUM_OUTPUTS as usize) {
            value_balance = value_balance.sub(record.value());
        }

        // Ensure the value balance matches the fee from the request.
        if value_balance != request.fee() {
            return Err(anyhow!(
                "Value balance does not match fee amount from request. Expected {} from request, found {} from response",
                request.fee(),
                value_balance
            ));
        }

        // Compute the transition ID.
        let transition_id = Transition::<N>::compute_transition_id(&serial_numbers, &commitments)?;

        // Construct the input value commitments.
        let input_record_values: Vec<AleoAmount> = request.records().iter().map(|x| x.value()).collect();

        let mut input_value_commitments = Vec::with_capacity(N::NUM_INPUTS as usize);
        let mut input_value_commitment_randomness = Vec::with_capacity(N::NUM_INPUTS as usize);

        for value in input_record_values.iter() {
            let commitment_randomness = N::ProgramScalarField::rand(rng);
            let commitment =
                N::value_commitment_scheme().commit_bytes(&value.to_bytes_le()?, &commitment_randomness)?;

            input_value_commitments.push(commitment.into());
            input_value_commitment_randomness.push(commitment_randomness);
        }

        // Construct the output value commitments.
        let output_record_values: Vec<AleoAmount> = output_records.iter().map(|x| x.value()).collect();

        let mut output_value_commitments = Vec::with_capacity(N::NUM_OUTPUTS as usize);
        let mut output_value_commitment_randomness = Vec::with_capacity(N::NUM_OUTPUTS as usize);

        for value in output_record_values.iter() {
            let commitment_randomness = N::ProgramScalarField::rand(rng);
            let commitment =
                N::value_commitment_scheme().commit_bytes(&value.to_bytes_le()?, &commitment_randomness)?;

            output_value_commitments.push(commitment.into());
            output_value_commitment_randomness.push(commitment_randomness);
        }

        // Construct the final value balance commitment.
        let value_balance_commitment = ValueBalanceCommitment::new(
            &input_value_commitments,
            &output_value_commitments,
            &input_value_commitment_randomness,
            &output_value_commitment_randomness,
            value_balance,
            &transition_id.to_bytes_le()?,
            rng,
        )?;

        // Construct the response.
        Response::new(
            transition_id,
            output_records,
            encryption_randomness,
            value_balance,
            input_value_commitments,
            output_value_commitments,
            input_value_commitment_randomness,
            output_value_commitment_randomness,
            value_balance_commitment.into(),
            events,
        )
    }
}

impl<N: Network> Default for ResponseBuilder<N> {
    fn default() -> Self {
        Self::new()
    }
}

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
//                 let account = Account::new(rng);
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
