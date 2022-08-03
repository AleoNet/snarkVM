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

mod leaf;
pub use leaf::*;

mod merkle;
pub use merkle::*;

mod bytes;
mod serialize;
mod string;

use crate::{
    ledger::{vm::VM, Origin, Transition},
    process::{Authorization, Deployment, Execution},
    program::Program,
};
use console::{
    account::PrivateKey,
    collections::merkle_tree::MerklePath,
    network::{prelude::*, BHPMerkleTree},
    program::{Identifier, Plaintext, ProgramID, Record, Value},
    types::{Field, Group},
};

/// An additional fee to be included in the transaction.
pub type AdditionalFee<N> = Transition<N>;

#[derive(Clone, PartialEq, Eq)]
pub enum Transaction<N: Network> {
    /// The transaction deployment publishes an Aleo program to the network.
    Deploy(N::TransactionID, Deployment<N>, AdditionalFee<N>),
    /// The transaction execution represents a call to an Aleo program.
    Execute(N::TransactionID, Execution<N>, Option<AdditionalFee<N>>),
}

impl<N: Network> Transaction<N> {
    /// Initializes a new deployment transaction.
    pub fn from_deployment(deployment: Deployment<N>, additional_fee: AdditionalFee<N>) -> Result<Self> {
        // Ensure the transaction is not empty.
        ensure!(!deployment.program().functions().is_empty(), "Attempted to create an empty transaction deployment");
        // Compute the transaction ID.
        let id = *Self::deployment_tree(&deployment, &additional_fee)?.root();
        // Construct the deployment transaction.
        Ok(Self::Deploy(id.into(), deployment, additional_fee))
    }

    /// Initializes a new execution transaction.
    pub fn from_execution(execution: Execution<N>, additional_fee: Option<AdditionalFee<N>>) -> Result<Self> {
        // Ensure the transaction is not empty.
        ensure!(!execution.is_empty(), "Attempted to create an empty transaction execution");
        // Compute the transaction ID.
        let id = *Self::execution_tree(&execution, &additional_fee)?.root();
        // Construct the execution transaction.
        Ok(Self::Execute(id.into(), execution, additional_fee))
    }
}

impl<N: Network> Transaction<N> {
    /// The maximum number of transitions allowed in a transaction.
    const MAX_TRANSITIONS: usize = usize::pow(2, TRANSACTION_DEPTH as u32);

    /// Initializes a new deployment transaction.
    pub fn deploy<R: Rng + CryptoRng>(
        vm: &VM<N>,
        private_key: &PrivateKey<N>,
        program: &Program<N>,
        (credits, additional_fee_in_gates): (Record<N, Plaintext<N>>, u64),
        rng: &mut R,
    ) -> Result<Self> {
        // Compute the deployment.
        let deployment = vm.deploy(program, rng)?;
        // Compute the additional fee.
        let (_, additional_fee) = vm.execute_additional_fee(private_key, credits, additional_fee_in_gates, rng)?;
        // Initialize the transaction.
        Self::from_deployment(deployment, additional_fee)
    }

    /// Initializes a new execution transaction from an authorization.
    pub fn execute_authorization<R: Rng + CryptoRng>(
        vm: &VM<N>,
        authorization: Authorization<N>,
        rng: &mut R,
    ) -> Result<Self> {
        // Compute the execution.
        let (_, execution) = vm.execute(authorization, rng)?;
        // Initialize the transaction.
        Self::from_execution(execution, None)
    }

    /// Initializes a new execution transaction from an authorization and additional fee.
    pub fn execute_authorization_with_additional_fee<R: Rng + CryptoRng>(
        vm: &VM<N>,
        private_key: &PrivateKey<N>,
        authorization: Authorization<N>,
        additional_fee: Option<(Record<N, Plaintext<N>>, u64)>,
        rng: &mut R,
    ) -> Result<Self> {
        // Compute the execution.
        let (_, execution) = vm.execute(authorization, rng)?;
        // Compute the additional fee, if it is present.
        let additional_fee = match additional_fee {
            Some((credits, additional_fee_in_gates)) => {
                Some(vm.execute_additional_fee(private_key, credits, additional_fee_in_gates, rng)?.1)
            }
            None => None,
        };
        // Initialize the transaction.
        Self::from_execution(execution, additional_fee)
    }

    /// Initializes a new execution transaction.
    pub fn execute<R: Rng + CryptoRng>(
        vm: &VM<N>,
        private_key: &PrivateKey<N>,
        program_id: &ProgramID<N>,
        function_name: Identifier<N>,
        inputs: &[Value<N>],
        additional_fee: Option<(Record<N, Plaintext<N>>, u64)>,
        rng: &mut R,
    ) -> Result<Self> {
        // Compute the authorization.
        let authorization = vm.authorize(private_key, program_id, function_name, inputs, rng)?;
        // Initialize the transaction.
        Self::execute_authorization_with_additional_fee(vm, private_key, authorization, additional_fee, rng)
    }
}

impl<N: Network> Transaction<N> {
    /// Returns the transaction ID.
    pub const fn id(&self) -> N::TransactionID {
        match self {
            Self::Deploy(id, ..) => *id,
            Self::Execute(id, ..) => *id,
        }
    }

    /// Returns an iterator over all executed transitions.
    pub fn transitions(&self) -> impl '_ + Iterator<Item = &Transition<N>> {
        match self {
            Self::Deploy(_, _, additional_fee) => [].iter().chain([Some(additional_fee)].into_iter().flatten()),
            Self::Execute(_, execution, additional_fee) => {
                execution.iter().chain([additional_fee.as_ref()].into_iter().flatten())
            }
        }
    }

    /// Returns an iterator over the transition IDs, for all transitions.
    pub fn transition_ids(&self) -> impl '_ + Iterator<Item = &N::TransitionID> {
        self.transitions().map(Transition::id)
    }

    /// Returns an iterator over the transition public keys, for all transitions.
    pub fn transition_public_keys(&self) -> impl '_ + Iterator<Item = &Group<N>> {
        self.transitions().map(Transition::tpk)
    }

    /// Returns an iterator over the origins, for all transition inputs that are records.
    pub fn origins(&self) -> impl '_ + Iterator<Item = &Origin<N>> {
        self.transitions().flat_map(Transition::origins)
    }

    /// Returns an iterator over the serial numbers, for all transition inputs that are records.
    pub fn serial_numbers(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transitions().flat_map(Transition::serial_numbers)
    }

    /// Returns an iterator over the commitments, for all transition outputs that are records.
    pub fn commitments(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transitions().flat_map(Transition::commitments)
    }

    /// Returns an iterator over the nonces, for all transition outputs that are records.
    pub fn nonces(&self) -> impl '_ + Iterator<Item = &Group<N>> {
        self.transitions().flat_map(Transition::nonces)
    }

    /// Returns an iterator over the fees, for all transitions.
    pub fn fees(&self) -> impl '_ + Iterator<Item = &i64> {
        self.transitions().map(Transition::fee)
    }
}
