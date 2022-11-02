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

impl<N: Network> Transaction<N> {
    /// Returns the transaction root, by computing the root for a Merkle tree of the transition IDs.
    pub fn to_root(&self) -> Result<Field<N>> {
        Ok(*self.to_tree()?.root())
    }

    /// Returns the Merkle leaf for the given ID of a function or transition in the transaction.
    pub fn to_leaf(&self, id: &Field<N>) -> Result<TransactionLeaf<N>> {
        match self {
            Self::Deploy(_, deployment, fee) => {
                // Check if the ID is the transition ID for the fee.
                if *id == **fee.id() {
                    // Return the transaction leaf.
                    return Ok(TransactionLeaf::new_deployment(
                        deployment.program().functions().len() as u16, // The last index.
                        *id,
                    ));
                }

                // Iterate through the functions in the deployment.
                for (index, function) in deployment.program().functions().values().enumerate() {
                    // Check if the function hash matches the given ID.
                    if *id == N::hash_bhp1024(&function.to_bytes_le()?.to_bits_le())? {
                        // Return the transaction leaf.
                        return Ok(TransactionLeaf::new_deployment(index as u16, *id));
                    }
                }
                // Error if the function hash was not found.
                bail!("Function hash not found in deployment transaction");
            }
            Self::Execute(_, execution, additional_fee) => {
                // Check if the ID is the transition ID for the additional fee, if it is present.
                if let Some(additional_fee) = additional_fee {
                    if *id == **additional_fee.id() {
                        // Return the transaction leaf.
                        return Ok(TransactionLeaf::new_execution(
                            execution.len() as u16, // The last index.
                            *id,
                        ));
                    }
                }

                // Iterate through the transitions in the execution.
                for (index, transition) in execution.transitions().enumerate() {
                    // Check if the transition ID matches the given ID.
                    if *id == **transition.id() {
                        // Return the transaction leaf.
                        return Ok(TransactionLeaf::new_execution(index as u16, *id));
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
            Transaction::Deploy(_, deployment, additional_fee) => Self::deployment_tree(deployment, additional_fee),
            // Compute the execution tree.
            Transaction::Execute(_, execution, additional_fee) => Self::execution_tree(execution, additional_fee),
        }
    }
}

impl<N: Network> Transaction<N> {
    /// Returns the Merkle tree for the given deployment.
    pub(super) fn deployment_tree(deployment: &Deployment<N>, fee: &Fee<N>) -> Result<TransactionTree<N>> {
        // Ensure the number of leaves is within the Merkle tree size.
        Self::check_deployment_size(deployment)?;
        // Retrieve the program.
        let program = deployment.program();
        // Prepare the leaves.
        let leaves = program
            .functions()
            .values()
            .enumerate()
            .map(|(index, function)| {
                // Construct the transaction leaf.
                Ok(TransactionLeaf::new_deployment(
                    index as u16,
                    N::hash_bhp1024(&function.to_bytes_le()?.to_bits_le())?,
                )
                .to_bits_le())
            })
            .chain(
                [Ok(TransactionLeaf::new_deployment(
                    program.functions().len() as u16, // The last index.
                    **fee.transition_id(),
                )
                .to_bits_le())]
                .into_iter(),
            );
        // Compute the deployment tree.
        N::merkle_tree_bhp::<TRANSACTION_DEPTH>(&leaves.collect::<Result<Vec<_>>>()?)
    }

    /// Returns the Merkle tree for the given execution.
    pub fn execution_tree(execution: &Execution<N>, additional_fee: &Option<Fee<N>>) -> Result<TransactionTree<N>> {
        // Ensure the number of leaves is within the Merkle tree size.
        Self::check_execution_size(execution)?;
        // Prepare the leaves.
        let leaves = execution.transitions().enumerate().map(|(index, transition)| {
            // Construct the transaction leaf.
            TransactionLeaf::new_execution(index as u16, **transition.id()).to_bits_le()
        });
        // If the additional fee is present, add it to the leaves.
        let leaves = match additional_fee {
            Some(additional_fee) => {
                // Construct the transaction leaf.
                let leaf = TransactionLeaf::new_execution(
                    execution.len() as u16, // The last index.
                    **additional_fee.transition_id(),
                )
                .to_bits_le();
                // Add the leaf to the leaves.
                leaves.chain([leaf].into_iter()).collect::<Vec<_>>()
            }
            None => leaves.collect::<Vec<_>>(),
        };

        // Compute the execution tree.
        N::merkle_tree_bhp::<TRANSACTION_DEPTH>(&leaves)
    }

    /// Returns `true` if the deployment is within the size bounds.
    pub fn check_deployment_size(deployment: &Deployment<N>) -> Result<()> {
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
            functions.len() < Self::MAX_TRANSITIONS, // Note: Observe we hold back 1 for the additional fee.
            "Deployment must contain less than {} functions, found {}",
            Self::MAX_TRANSITIONS,
            functions.len()
        );
        Ok(())
    }

    /// Returns `true` if the execution is within the size bounds.
    pub fn check_execution_size(execution: &Execution<N>) -> Result<()> {
        // Ensure the number of functions is within the allowed range.
        ensure!(
            execution.len() < Self::MAX_TRANSITIONS, // Note: Observe we hold back 1 for the additional fee.
            "Execution must contain less than {} transitions, found {}",
            Self::MAX_TRANSITIONS,
            execution.len()
        );
        Ok(())
    }
}
