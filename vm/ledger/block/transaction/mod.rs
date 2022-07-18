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
    console::{
        collections::merkle_tree::MerklePath,
        network::{prelude::*, BHPMerkleTree},
        types::{Field, Group},
    },
    ledger::vm::VM,
};
use snarkvm_compiler::{Deployment, Execution, Transition};

#[derive(Clone, PartialEq, Eq)]
pub enum Transaction<N: Network> {
    /// The transaction deployment publishes an Aleo program to the network.
    Deploy(N::TransactionID, Deployment<N>),
    /// The transaction execution represents a call to an Aleo program.
    Execute(N::TransactionID, Execution<N>),
}

impl<N: Network> Transaction<N> {
    /// The maximum number of transitions allowed in a transaction.
    const MAX_TRANSITIONS: usize = usize::pow(2, TRANSACTION_DEPTH as u32);

    /// Initializes a new deployment transaction.
    pub fn deploy(deployment: Deployment<N>) -> Result<Self> {
        // Ensure the transaction is not empty.
        ensure!(!deployment.program().functions().is_empty(), "Attempted to create an empty transaction deployment");
        // Compute the transaction ID.
        let id = *Self::deployment_tree(&deployment)?.root();
        // Construct the deployment transaction.
        Ok(Self::Deploy(id.into(), deployment))
    }

    /// Initializes a new execution transaction.
    pub fn execute(execution: Execution<N>) -> Result<Self> {
        // Ensure the transaction is not empty.
        ensure!(!execution.is_empty(), "Attempted to create an empty transaction execution");
        // Compute the transaction ID.
        let id = *Self::execution_tree(&execution)?.root();
        // Construct the execution transaction.
        Ok(Self::Execute(id.into(), execution))
    }

    /// Returns `true` if the transaction is well-formed.
    pub fn verify(&self, vm: &VM<N>) -> bool {
        // Compute the Merkle root of the transaction.
        match self.to_root() {
            // Ensure the transaction ID is correct.
            Ok(root) => {
                if *self.id() != root {
                    warn!("Incorrect transaction ID ({})", self.id());
                    return false;
                }
            }
            Err(error) => {
                warn!("Failed to compute the Merkle root of the transaction: {error}\n{self}");
                return false;
            }
        };

        match self {
            Transaction::Deploy(_, deployment) => {
                // Check the deployment size.
                if let Err(error) = Self::check_deployment_size(deployment) {
                    warn!("Invalid transaction (deployment): {error}");
                    return false;
                }
                // Verify the deployment.
                vm.verify_deployment(deployment)
            }
            Transaction::Execute(_, execution) => {
                // Check the deployment size.
                if let Err(error) = Self::check_execution_size(execution) {
                    warn!("Invalid transaction (execution): {error}");
                    return false;
                }
                // Verify the execution.
                vm.verify_execution(execution)
            }
        }
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
            Self::Deploy(..) => [].iter(),
            Self::Execute(.., execution) => execution.iter(),
        }
    }

    /// Returns an iterator over the transition IDs, for all executed transitions.
    pub fn transition_ids(&self) -> impl '_ + Iterator<Item = &N::TransitionID> {
        match self {
            Self::Deploy(..) => [].iter().map(Transition::id),
            Self::Execute(.., execution) => execution.iter().map(Transition::id),
        }
    }

    /// Returns an iterator over the transition public keys, for all executed transitions.
    pub fn transition_public_keys(&self) -> impl '_ + Iterator<Item = &Group<N>> {
        match self {
            Self::Deploy(..) => [].iter().map(Transition::tpk),
            Self::Execute(.., execution) => execution.iter().map(Transition::tpk),
        }
    }

    /// Returns an iterator over the serial numbers, for all executed transition inputs that are records.
    pub fn serial_numbers(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        match self {
            Self::Deploy(..) => [].iter().flat_map(Transition::serial_numbers),
            Self::Execute(.., execution) => execution.iter().flat_map(Transition::serial_numbers),
        }
    }

    /// Returns an iterator over the commitments, for all executed transition outputs that are records.
    pub fn commitments(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        match self {
            Self::Deploy(..) => [].iter().flat_map(Transition::commitments),
            Self::Execute(.., execution) => execution.iter().flat_map(Transition::commitments),
        }
    }

    /// Returns an iterator over the nonces, for all executed transition outputs that are records.
    pub fn nonces(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        match self {
            Self::Deploy(..) => [].iter().flat_map(Transition::nonces),
            Self::Execute(.., execution) => execution.iter().flat_map(Transition::nonces),
        }
    }
}
