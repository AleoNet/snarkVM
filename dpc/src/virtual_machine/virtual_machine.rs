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

use crate::{circuits::*, prelude::*};
use snarkvm_algorithms::{merkle_tree::MerklePath, prelude::*};

use anyhow::{anyhow, Result};
use itertools::Itertools;
use rand::{CryptoRng, Rng};
use std::sync::Arc;

#[derive(Clone, Debug)]
pub struct VirtualMachine<N: Network> {
    /// The root of the ledger tree used to prove inclusion of ledger-consumed records.
    ledger_root: N::LedgerRoot,
    /// The local transitions tree.
    local_transitions: Transitions<N>,
    /// The current list of transitions.
    transitions: Vec<Transition<N>>,
}

impl<N: Network> VirtualMachine<N> {
    /// Initializes a new instance of the virtual machine, with the given request.
    pub fn new(ledger_root: N::LedgerRoot) -> Result<Self> {
        Ok(Self { ledger_root, local_transitions: Transitions::new()?, transitions: Default::default() })
    }

    /// Returns the local proof for a given commitment.
    pub fn to_local_proof(&self, commitment: N::Commitment) -> Result<LocalProof<N>> {
        self.local_transitions.to_local_proof(commitment)
    }

    /// Returns the number of transitions in the virtual machine.
    pub fn num_transitions(&self) -> usize {
        self.transitions.len()
    }

    /// Executes the request, returning a transaction.
    pub fn execute<R: Rng + CryptoRng>(mut self, request: &Request<N>, rng: &mut R) -> Result<(Self, Response<N>)> {
        // Ensure the request is valid.
        if !request.is_valid() {
            return Err(anyhow!("Virtual machine received an invalid request"));
        }

        // Compute the operation.
        let operation = request.operation().clone();
        let response = match operation {
            Operation::Noop => Self::noop(request, rng)?,
            Operation::Coinbase(recipient, amount) => Self::coinbase(request, recipient, amount, rng)?,
            Operation::Transfer(caller, recipient, amount) => Self::transfer(request, caller, recipient, amount, rng)?,
            Operation::Evaluate(function_id, function_inputs) => self.evaluate(
                request,
                request.to_program_id()?,
                &function_id,
                &function_inputs,
                vec![], // custom_events
                rng,
            )?,
        };

        let program_id = request.to_program_id()?;

        // TODO (raychu86): Clean this up.
        // Compute the input circuit proofs.
        let mut input_proofs = Vec::with_capacity(N::NUM_INPUTS as usize);
        for (
            ((((record, serial_number), ledger_proof), signature), input_value_commitment),
            input_value_commitment_randomness,
        ) in request
            .records()
            .iter()
            .zip_eq(request.to_serial_numbers()?.iter())
            .zip_eq(request.ledger_proofs())
            .zip_eq(request.signatures())
            .zip_eq(response.input_value_commitments())
            .zip_eq(response.input_value_commitment_randomness())
        {
            let input_public = InputPublicVariables::<N>::new(
                *serial_number,
                input_value_commitment.clone(),
                self.ledger_root,
                self.local_transitions.root(),
                program_id,
            );
            let input_private = InputPrivateVariables::<N>::new(
                record.clone(),
                ledger_proof.clone(),
                signature.clone(),
                *input_value_commitment_randomness,
            )?;

            let input_circuit = InputCircuit::<N>::new(input_public.clone(), input_private);
            let input_proof = N::InputSNARK::prove(N::input_proving_key(), &input_circuit, rng)?;

            assert!(N::InputSNARK::verify(N::input_verifying_key(), &input_public, &input_proof)?);

            input_proofs.push(input_proof.into());
        }

        // TODO (raychu86): Clean this up.
        // Compute the output circuit proofs.
        let mut output_proofs = Vec::with_capacity(N::NUM_OUTPUTS as usize);
        for (
            (((record, commitment), encryption_randomness), output_value_commitment),
            output_value_commitment_randomness,
        ) in response
            .records()
            .iter()
            .zip_eq(response.commitments())
            .zip_eq(response.encryption_randomness())
            .zip_eq(response.output_value_commitments())
            .zip_eq(response.output_value_commitment_randomness())
        {
            let output_public =
                OutputPublicVariables::<N>::new(commitment, output_value_commitment.clone(), program_id);
            let output_private = OutputPrivateVariables::<N>::new(
                record.clone(),
                *encryption_randomness,
                *output_value_commitment_randomness,
            )?;

            let output_circuit = OutputCircuit::<N>::new(output_public.clone(), output_private);
            let output_proof = N::OutputSNARK::prove(N::output_proving_key(), &output_circuit, rng)?;

            assert!(N::OutputSNARK::verify(N::output_verifying_key(), &output_public, &output_proof)?);

            output_proofs.push(output_proof.into());
        }

        // Compute the noop execution, for now.
        let execution = Execution::from(None, input_proofs, output_proofs)?;

        // Construct the transition.
        let transition = Transition::<N>::new(request, &response, execution)?;

        // Update the state of the virtual machine.
        self.local_transitions.add(&transition)?;
        self.transitions.push(transition);

        Ok((self, response))
    }

    /// Finalizes the virtual machine state and returns a transaction.
    pub fn finalize(&self) -> Result<Transaction<N>> {
        Transaction::from(*N::input_circuit_id(), *N::output_circuit_id(), self.ledger_root, self.transitions.clone())
    }

    /// Performs a noop transition.
    fn noop<R: Rng + CryptoRng>(request: &Request<N>, rng: &mut R) -> Result<Response<N>> {
        ResponseBuilder::new().add_request(request.clone()).build(rng)
    }

    /// Generates the given `amount` to `recipient`.
    fn coinbase<R: Rng + CryptoRng>(
        request: &Request<N>,
        recipient: Address<N>,
        amount: AleoAmount,
        rng: &mut R,
    ) -> Result<Response<N>> {
        ResponseBuilder::new()
            .add_request(request.clone())
            .add_output(Output::new(recipient, amount, None, None)?)
            .build(rng)
    }

    // TODO (raychu86): Add support for multiple recipients.
    /// Transfers the given `amount` from `caller` to `recipient`.
    fn transfer<R: Rng + CryptoRng>(
        request: &Request<N>,
        caller: Address<N>,
        recipient: Address<N>,
        amount: AleoAmount,
        rng: &mut R,
    ) -> Result<Response<N>> {
        // Fetch the caller.
        if request.caller()? != caller {
            return Err(anyhow!("Caller in instruction does not match request caller"));
        }

        // Compute the starting balance of the caller.
        let starting_balance = request.to_balance().sub(request.fee());
        if starting_balance.is_negative() {
            return Err(VMError::BalanceInsufficient.into());
        }

        // Compute the final balance of the caller.
        let caller_balance = starting_balance.sub(amount);
        if caller_balance.is_negative() {
            return Err(VMError::BalanceInsufficient.into());
        }

        ResponseBuilder::new()
            .add_request(request.clone())
            .add_output(Output::new(caller, caller_balance, None, None)?)
            .add_output(Output::new(recipient, amount, None, None)?)
            .build(rng)
    }

    /// Returns a response based on the current state of the virtual machine.
    fn evaluate<R: Rng + CryptoRng>(
        &self,
        request: &Request<N>,
        program_id: Option<N::ProgramID>,
        function_id: &N::FunctionID,
        function_inputs: &FunctionInputs<N>,
        custom_events: Vec<Vec<u8>>,
        rng: &mut R,
    ) -> Result<Response<N>> {
        // TODO (raychu86): Do function type checks.

        // Check that the function id exists in the program.

        // Check that the function id is the same as the request.
        if Some(*function_id) != request.function_id() {
            return Err(anyhow!("Invalid function id"));
        }

        // Fetch the caller.
        if request.caller()? != function_inputs.caller {
            return Err(anyhow!("Caller in instruction does not match request caller"));
        }

        // Compute the starting balance of the caller.
        let starting_balance = request.to_balance().sub(request.fee());
        if starting_balance.is_negative() {
            return Err(VMError::BalanceInsufficient.into());
        }

        // Compute the final balance of the caller.
        let caller_balance = starting_balance.sub(function_inputs.amount);
        if caller_balance.is_negative() {
            return Err(VMError::BalanceInsufficient.into());
        }

        let mut response_builder = ResponseBuilder::new().add_request(request.clone()).add_output(Output::new(
            function_inputs.recipient,
            function_inputs.amount,
            Some(function_inputs.record_payload.clone()),
            program_id,
        )?);

        // Add the change address if the balance is not zero.
        if !caller_balance.is_zero() {
            response_builder =
                response_builder.add_output(Output::new(function_inputs.caller, caller_balance, None, None)?)
        }

        // Add custom events to the response.
        for event in custom_events {
            response_builder = response_builder.add_event(Event::Custom(event));
        }

        // Add the operation event to the response builder.
        if request.is_public() {
            response_builder = response_builder.add_event(Event::Operation(request.operation().clone()));
        }

        response_builder.build(rng)
    }

    // TODO (raychu86): Temporary solution. Handle execution elsewhere.
    /// Executes the request of a particular program execution and returns a transaction.
    pub fn execute_program<R: Rng + CryptoRng>(
        mut self,
        request: &Request<N>,
        program_id: <N as Network>::ProgramID,
        function: &Arc<dyn Function<N>>,
        function_path: &MerklePath<<N as Network>::ProgramIDParameters>,
        function_verifying_key: <<N as Network>::ProgramSNARK as SNARK>::VerifyingKey,
        private_variables: &dyn ProgramPrivateVariables<N>,
        custom_events: Vec<Vec<u8>>,
        rng: &mut R,
    ) -> Result<(Self, Response<N>)> {
        // Ensure the request is valid.
        if !request.is_valid() {
            return Err(anyhow!("Virtual machine received an invalid request"));
        }

        // Compute the operation.
        let operation = request.operation().clone();
        let response = match operation {
            Operation::Evaluate(function_id, function_inputs) => {
                self.evaluate(request, Some(program_id), &function_id, &function_inputs, custom_events, rng)?
            }
            _ => return Err(anyhow!("Invalid Operation")),
        };

        let transition_id = response.transition_id();

        // Compute the execution.
        let program_proof = function.execute(ProgramPublicVariables::new(transition_id), private_variables)?;
        let public_variables = ProgramPublicVariables::new(transition_id);

        assert!(function.verify(&public_variables, &program_proof));
        assert!(function_path.verify(&program_id, &function.function_id())?);

        // TODO (raychu86): Clean this up.
        // Compute the input circuit proofs.
        let mut input_proofs = Vec::with_capacity(N::NUM_INPUTS as usize);
        for (
            ((((record, serial_number), ledger_proof), signature), input_value_commitment),
            input_value_commitment_randomness,
        ) in request
            .records()
            .iter()
            .zip_eq(request.to_serial_numbers()?.iter())
            .zip_eq(request.ledger_proofs())
            .zip_eq(request.signatures())
            .zip_eq(response.input_value_commitments())
            .zip_eq(response.input_value_commitment_randomness())
        {
            let input_public = InputPublicVariables::<N>::new(
                *serial_number,
                input_value_commitment.clone(),
                self.ledger_root,
                self.local_transitions.root(),
                Some(program_id),
            );
            let input_private = InputPrivateVariables::<N>::new(
                record.clone(),
                ledger_proof.clone(),
                signature.clone(),
                *input_value_commitment_randomness,
            )?;

            let input_circuit = InputCircuit::<N>::new(input_public.clone(), input_private);
            let input_proof = N::InputSNARK::prove(N::input_proving_key(), &input_circuit, rng)?;

            assert!(N::InputSNARK::verify(N::input_verifying_key(), &input_public, &input_proof)?);

            input_proofs.push(input_proof.into());
        }

        // TODO (raychu86): Clean this up.
        // Compute the output circuit proofs.
        let mut output_proofs = Vec::with_capacity(N::NUM_OUTPUTS as usize);
        for (
            (((record, commitment), encryption_randomness), output_value_commitment),
            output_value_commitment_randomness,
        ) in response
            .records()
            .iter()
            .zip_eq(response.commitments())
            .zip_eq(response.encryption_randomness())
            .zip_eq(response.output_value_commitments())
            .zip_eq(response.output_value_commitment_randomness())
        {
            let output_public =
                OutputPublicVariables::<N>::new(commitment, output_value_commitment.clone(), Some(program_id));
            let output_private = OutputPrivateVariables::<N>::new(
                record.clone(),
                *encryption_randomness,
                *output_value_commitment_randomness,
            )?;

            let output_circuit = OutputCircuit::<N>::new(output_public.clone(), output_private);
            let output_proof = N::OutputSNARK::prove(N::output_proving_key(), &output_circuit, rng)?;

            assert!(N::OutputSNARK::verify(N::output_verifying_key(), &output_public, &output_proof)?);

            output_proofs.push(output_proof.into());
        }

        let execution = Execution::from(
            Some(ProgramExecution::from(program_id, function_path.clone(), function_verifying_key, program_proof)?),
            input_proofs,
            output_proofs,
        )?;

        // Construct the transition.
        let transition = Transition::<N>::new(request, &response, execution)?;

        // Update the state of the virtual machine.
        self.local_transitions.add(&transition)?;
        self.transitions.push(transition);

        Ok((self, response))
    }
}
