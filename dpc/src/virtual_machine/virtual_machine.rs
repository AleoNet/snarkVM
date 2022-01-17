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

use crate::{circuits::*, prelude::*};
use snarkvm_algorithms::{merkle_tree::MerklePath, prelude::*};

use anyhow::{anyhow, Result};
use rand::{CryptoRng, Rng};
use std::sync::Arc;

#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"), Debug(bound = "N: Network"))]
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
        Ok(Self {
            ledger_root,
            local_transitions: Transitions::new()?,
            transitions: Default::default(),
        })
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
            Operation::Evaluate(function_id, function_type, function_inputs) => self.evaluate(
                request,
                request.to_program_id()?,
                &function_id,
                &function_type,
                &function_inputs,
                vec![], // custom_events
                rng,
            )?,
        };

        let program_id = request.to_program_id()?;
        let transition_id = response.transition_id();
        let value_balance = response.value_balance();

        // Compute the inner circuit proof, and verify that the inner proof passes.
        let inner_public = InnerPublicVariables::new(
            transition_id,
            value_balance,
            self.ledger_root,
            self.local_transitions.root(),
            Some(program_id),
        );
        let inner_private = InnerPrivateVariables::new(request, &response)?;
        let inner_circuit = InnerCircuit::<N>::new(inner_public, inner_private);
        let inner_proof = N::InnerSNARK::prove(N::inner_proving_key(), &inner_circuit, rng)?;

        assert!(N::InnerSNARK::verify(
            N::inner_verifying_key(),
            &inner_public,
            &inner_proof
        )?);

        // Compute the noop execution, for now.
        let execution = Execution::from(
            *N::noop_program_id(),
            N::noop_program_path().clone(),
            N::noop_circuit_verifying_key().clone(),
            Noop::<N>::new().execute(
                ProgramPublicVariables::new(transition_id),
                &NoopPrivateVariables::<N>::new_blank()?,
            )?,
            inner_proof.into(),
        )?;

        // Construct the transition.
        let transition = Transition::<N>::new(request, &response, execution)?;

        // Update the state of the virtual machine.
        self.local_transitions.add(&transition)?;
        self.transitions.push(transition);

        Ok((self, response))
    }

    /// Finalizes the virtual machine state and returns a transaction.
    pub fn finalize(&self) -> Result<Transaction<N>> {
        Transaction::from(*N::inner_circuit_id(), self.ledger_root, self.transitions.clone())
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
            .add_output(Output::new(recipient, amount, Default::default(), None)?)
            .build(rng)
    }

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
            .add_output(Output::new(caller, caller_balance, Default::default(), None)?)
            .add_output(Output::new(recipient, amount, Default::default(), None)?)
            .build(rng)
    }

    /// Returns a response based on the current state of the virtual machine.
    fn evaluate<R: Rng + CryptoRng>(
        &self,
        request: &Request<N>,
        program_id: N::ProgramID,
        function_id: &N::FunctionID,
        _function_type: &FunctionType,
        function_inputs: &FunctionInputs<N>,
        custom_events: Vec<Vec<u8>>,
        rng: &mut R,
    ) -> Result<Response<N>> {
        // TODO (raychu86): Do function type checks.

        // Check that the function id exists in the program.

        // Check that the function id is the same as the request.
        if function_id != &request.function_id() {
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

        let mut response_builder = ResponseBuilder::new()
            .add_request(request.clone())
            .add_output(Output::new(
                function_inputs.recipient,
                function_inputs.amount,
                function_inputs.record_payload.clone(),
                Some(program_id),
            )?);

        // Add the change address if the balance is not zero.
        if !caller_balance.is_zero() {
            response_builder = response_builder.add_output(Output::new(
                function_inputs.caller,
                caller_balance,
                Default::default(),
                None,
            )?)
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
            Operation::Evaluate(function_id, function_type, function_inputs) => self.evaluate(
                request,
                program_id,
                &function_id,
                &function_type,
                &function_inputs,
                custom_events,
                rng,
            )?,
            _ => return Err(anyhow!("Invalid Operation")),
        };

        let transition_id = response.transition_id();
        let value_balance = response.value_balance();

        // Compute the execution.
        let program_proof = function.execute(ProgramPublicVariables::new(transition_id), private_variables)?;
        let public_variables = ProgramPublicVariables::new(transition_id);

        assert!(function.verify(&public_variables, &program_proof));
        assert!(function_path.verify(&program_id, &function.function_id())?);

        // Compute the inner circuit proof, and verify that the inner proof passes.
        let inner_public = InnerPublicVariables::new(
            transition_id,
            value_balance,
            self.ledger_root,
            self.local_transitions.root(),
            Some(program_id),
        );
        let inner_private = InnerPrivateVariables::new(request, &response)?;
        let inner_circuit = InnerCircuit::<N>::new(inner_public, inner_private);
        let inner_proof = N::InnerSNARK::prove(N::inner_proving_key(), &inner_circuit, rng)?;

        assert!(N::InnerSNARK::verify(
            N::inner_verifying_key(),
            &inner_public,
            &inner_proof
        )?);

        let execution = Execution::from(
            program_id,
            function_path.clone(),
            function_verifying_key,
            program_proof,
            inner_proof.into(),
        )?;

        // Construct the transition.
        let transition = Transition::<N>::new(request, &response, execution)?;

        // Update the state of the virtual machine.
        self.local_transitions.add(&transition)?;
        self.transitions.push(transition);

        Ok((self, response))
    }
}
