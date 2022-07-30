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

use super::*;

/// The depth of the Merkle tree for the transaction.
pub(super) const TRANSACTION_DEPTH: u8 = 4;

/// The Merkle tree for the transaction.
type TransactionTree<N> = BHPMerkleTree<N, TRANSACTION_DEPTH>;
/// The Merkle path for a function or transition in the transaction.
pub type TransactionPath<N> = MerklePath<N, TRANSACTION_DEPTH>;

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
}

impl<N: Network> Transaction<N> {
    /// Returns the Merkle tree for the given deployment.
    pub(super) fn deployment_tree(deployment: &Deployment<N>) -> Result<TransactionTree<N>> {
        // Ensure the number of leaves is within the Merkle tree size.
        Self::check_deployment_size(deployment)?;
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
    pub(super) fn execution_tree(execution: &Execution<N>) -> Result<TransactionTree<N>> {
        // Ensure the number of leaves is within the Merkle tree size.
        Self::check_execution_size(execution)?;
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

    /// Returns `true` if the deployment is within the size bounds.
    pub(super) fn check_deployment_size(deployment: &Deployment<N>) -> Result<()> {
        // Retrieve the program.
        let program = deployment.program();
        // Retrieve the functions.
        let functions = program.functions();
        // Retrieve the verifying keys.
        let verifying_keys = deployment.verifying_keys();

        // Ensure the number of functions and verifying keys match.
        ensure!(
            functions.len() == verifying_keys.len(),
            "Number of functions ('{}') and verifying keys ('{}') do not match",
            functions.len(),
            verifying_keys.len()
        );
        // Ensure the number of functions is within the allowed range.
        ensure!(
            functions.len() <= Self::MAX_TRANSITIONS,
            "Deployment cannot exceed {} functions, found {}",
            Self::MAX_TRANSITIONS,
            functions.len()
        );
        Ok(())
    }

    /// Returns `true` if the execution is within the size bounds.
    pub(super) fn check_execution_size(execution: &Execution<N>) -> Result<()> {
        // Ensure the number of functions is within the allowed range.
        ensure!(
            execution.len() <= Self::MAX_TRANSITIONS,
            "Execution cannot exceed {} transitions, found {}",
            Self::MAX_TRANSITIONS,
            execution.len()
        );
        Ok(())
    }
}
