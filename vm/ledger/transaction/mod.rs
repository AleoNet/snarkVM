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

mod bytes;
mod serialize;
mod string;

use crate::console::{
    collections::merkle_tree::MerklePath,
    network::{prelude::*, BHPMerkleTree},
    types::{Field, Group},
};
use snarkvm_compiler::{Deployment, Execution, Transition};

/// The depth of the Merkle tree for the transaction.
const TRANSACTION_DEPTH: u8 = 4;

/// The Merkle tree for the transaction.
type TransactionTree<N> = BHPMerkleTree<N, TRANSACTION_DEPTH>;
/// The Merkle path for a function or transition in the transaction.
pub type TransactionPath<N> = MerklePath<N, TRANSACTION_DEPTH>;

#[derive(Clone, PartialEq, Eq)]
pub enum Transaction<N: Network> {
    /// The transaction deployment publishes an Aleo program to the network.
    Deploy(N::TransactionID, Deployment<N>),
    /// The transaction execution represents a call to an Aleo program.
    Execute(N::TransactionID, Execution<N>),
}

impl<N: Network> Transaction<N> {
    /// Initializes a new deployment transaction.
    pub fn deploy(deployment: Deployment<N>) -> Result<Self> {
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

impl<N: Network> Transaction<N> {
    /// Returns the transaction root, by computing the root for a Merkle tree of the transition IDs.
    pub fn to_root(&self) -> Result<Field<N>> {
        Ok(*self.to_tree()?.root())
    }

    /// Returns the Merkle leaf for the given ID of a function or transition in the transaction.
    pub fn to_leaf(&self, id: &Field<N>) -> Result<TransactionLeaf<N>> {
        match self {
            Self::Deploy(_, deployment) => {
                // Iterate through the functions in the deployment.
                for (index, function) in deployment.program().functions().values().enumerate() {
                    // Check if the function ID matches the given ID.
                    if *id == N::hash_bhp1024(&function.to_bytes_le()?.to_bits_le())? {
                        // Return the transaction leaf.
                        return Ok(TransactionLeaf::new(
                            0u8,
                            index as u16,
                            *deployment.program().id(),
                            *function.name(),
                            *id,
                        ));
                    }
                }
                // Error if the function ID was not found.
                bail!("Function ID not found in deployment transaction");
            }
            Self::Execute(_, execution) => {
                // Iterate through the transitions in the execution.
                for (index, transition) in execution.iter().enumerate() {
                    // Check if the transition ID matches the given ID.
                    if *id == **transition.id() {
                        // Return the transaction leaf.
                        return Ok(TransactionLeaf::new(
                            1u8,
                            index as u16,
                            *transition.program_id(),
                            *transition.function_name(),
                            *id,
                        ));
                    }
                }
                // Error if the transition ID was not found.
                bail!("Transition ID not found in execution transaction");
            }
        }
    }

    /// Returns the Merkle path for the transaction leaf.
    pub fn to_path(&self, leaf: &TransactionLeaf<N>) -> Result<TransactionPath<N>> {
        // Compute the Merkle path.
        self.to_tree()?.prove(leaf.index() as usize, &leaf.to_bits_le())
    }

    /// The Merkle tree of transition IDs for the transaction.
    pub fn to_tree(&self) -> Result<TransactionTree<N>> {
        match self {
            // Compute the deployment tree.
            Transaction::Deploy(_, deployment) => Self::deployment_tree(deployment),
            // Compute the execution tree.
            Transaction::Execute(_, execution) => Self::execution_tree(execution),
        }
    }

    /// Returns the Merkle tree for the given deployment.
    fn deployment_tree(deployment: &Deployment<N>) -> Result<TransactionTree<N>> {
        // Set the variant.
        let variant = 0u8;
        // Retrieve the program.
        let program = deployment.program();
        // Prepare the leaves.
        let leaves = program.functions().values().enumerate().map(|(index, function)| {
            // Construct the leaf as (variant || index || program ID || function name || Hash(function)).
            Ok(TransactionLeaf::new(
                variant,
                index as u16,
                *program.id(),
                *function.name(),
                N::hash_bhp1024(&function.to_bytes_le()?.to_bits_le())?,
            )
            .to_bits_le())
        });
        // Compute the deployment tree.
        N::merkle_tree_bhp::<TRANSACTION_DEPTH>(&leaves.collect::<Result<Vec<_>>>()?)
    }

    /// Returns the Merkle tree for the given execution.
    fn execution_tree(execution: &Execution<N>) -> Result<TransactionTree<N>> {
        // Set the variant.
        let variant = 1u8;
        // Prepare the leaves.
        let leaves = execution.iter().enumerate().map(|(index, transition)| {
            // Construct the leaf as (variant || index || program ID || function name || transition ID).
            TransactionLeaf::new(
                variant,
                index as u16,
                *transition.program_id(),
                *transition.function_name(),
                **transition.id(),
            )
            .to_bits_le()
        });
        // Compute the execution tree.
        N::merkle_tree_bhp::<TRANSACTION_DEPTH>(&leaves.collect::<Vec<_>>())
    }
}
