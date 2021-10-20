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
use snarkvm_algorithms::prelude::*;

use anyhow::{anyhow, Result};
use rand::{CryptoRng, Rng};

pub struct VirtualMachine<N: Network> {
    /// The local commitments tree.
    local_commitments: LocalCommitments<N>,
    /// The current list of transitions.
    transitions: Vec<Transition<N>>,
    /// The current list of events.
    events: Vec<Event<N>>,
}

impl<N: Network> VirtualMachine<N> {
    /// Initializes a new instance of the virtual machine, with the given request.
    pub fn new() -> Result<Self> {
        Ok(Self {
            local_commitments: LocalCommitments::new()?,
            transitions: Default::default(),
            events: Default::default(),
        })
    }

    /// Executes the request, returning a transaction.
    pub fn execute<R: Rng + CryptoRng>(mut self, request: &Request<N>, rng: &mut R) -> Result<Self> {
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
            Operation::Evaluate(..) => self.evaluate(rng)?,
        };

        let program_id = request.to_program_id()?;
        let transition_id = response.transition_id();

        // Compute the noop execution, for now.
        let execution = Execution {
            program_id: *N::noop_program_id(),
            program_path: N::noop_program_path().clone(),
            verifying_key: N::noop_circuit_verifying_key().clone(),
            proof: Noop::<N>::new().execute(ProgramPublicVariables::new(transition_id))?,
        };

        // Compute the inner circuit proof, and verify that the inner proof passes.
        let inner_public = InnerPublicVariables::new(transition_id, Some(program_id));
        let inner_private = InnerPrivateVariables::new(request, &response)?;
        let inner_circuit = InnerCircuit::<N>::new(inner_public.clone(), inner_private);
        let inner_proof = N::InnerSNARK::prove(N::inner_proving_key(), &inner_circuit, rng)?;

        assert!(N::InnerSNARK::verify(
            N::inner_verifying_key(),
            &inner_public,
            &inner_proof
        )?);

        // Construct the outer circuit public and private variables.
        let outer_public = OuterPublicVariables::new(transition_id, *N::inner_circuit_id());
        let outer_private = OuterPrivateVariables::new(N::inner_verifying_key().clone(), inner_proof, execution);
        let outer_circuit = OuterCircuit::<N>::new(outer_public.clone(), outer_private);
        let outer_proof = N::OuterSNARK::prove(N::outer_proving_key(), &outer_circuit, rng)?;

        assert!(N::OuterSNARK::verify(
            N::outer_verifying_key(),
            &outer_public,
            &outer_proof
        )?);

        // Construct the transition.
        let transition = Transition::<N>::new(request, &response, outer_proof)?;

        // Update the state of the virtual machine.
        self.local_commitments.add(transition.commitments())?;
        self.transitions.push(transition);
        self.events.extend_from_slice(response.events());

        Ok(self)
    }

    /// Finalizes the virtual machine state and returns a transaction.
    pub fn finalize(&self) -> Result<Transaction<N>> {
        Transaction::from(
            N::NETWORK_ID,
            *N::inner_circuit_id(),
            self.transitions.clone(),
            self.events.clone(),
        )
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
    fn evaluate<R: Rng + CryptoRng>(&self, _rng: &mut R) -> Result<Response<N>> {
        unimplemented!()
    }
}
