// Copyright (C) 2019-2023 Aleo Systems Inc.
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

impl<N: Network> Inclusion<N> {
    /// Returns the inclusion assignments for the given execution.
    pub async fn prepare_execution_wasm(
        &self,
        execution: &Execution<N>,
        url: &str,
    ) -> Result<(Vec<InclusionAssignment<N>>, N::StateRoot)> {
        // Ensure the number of leaves is within the Merkle tree size.
        Transaction::check_execution_size(execution)?;

        // Ensure the inclusion proof in the execution is 'None'.
        if execution.inclusion_proof().is_some() {
            bail!("Inclusion proof in the execution should not be set in 'Inclusion::prepare_execution'")
        }

        // Initialize an empty transaction tree.
        let mut transaction_tree = N::merkle_tree_bhp::<TRANSACTION_DEPTH>(&[])?;
        // Initialize a vector for the assignments.
        let mut assignments = vec![];

        // Retrieve the global state root.
        let global_state_root: N::StateRoot = reqwest::get(&format!("{url}/testnet3/latest/stateRoot"))
            .await
            .map_err(|e| anyhow!("Failed to get state path from the server: {}", e))?
            .json()
            .await?;

        // Ensure the global state root is not zero.
        if *global_state_root == Field::zero() {
            bail!("Inclusion expected the global state root in the execution to *not* be zero")
        }

        for (transition_index, transition) in execution.transitions().enumerate() {
            // Construct the transaction leaf.
            let transaction_leaf = TransactionLeaf::new_execution(transition_index as u16, **transition.id());

            // Process the input tasks.
            match self.input_tasks.get(transition.id()) {
                Some(tasks) => {
                    for task in tasks {
                        // Retrieve the local state root.
                        let local_state_root = (*transaction_tree.root()).into();

                        // Construct the state path.
                        let state_path = match task.is_local {
                            true => {
                                // Compute the transaction path.
                                let transaction_path =
                                    transaction_tree.prove(transition_index, &transaction_leaf.to_bits_le())?;
                                // Compute the transition leaf.
                                let transition_leaf = task.leaf;
                                // Compute the transition path.
                                let transition_path = transition.to_path(&transition_leaf)?;
                                // Output the state path.
                                StatePath::new_local(
                                    global_state_root,
                                    local_state_root,
                                    transaction_path,
                                    transaction_leaf,
                                    transition_path,
                                    transition_leaf,
                                )?
                            }
                            false => {
                                let commitment = &task.commitment;
                                reqwest::get(&format!("{url}/testnet3/statePath/{commitment}"))
                                    .await
                                    .map_err(|e| anyhow!("Failed to get state path from the server: {}", e))?
                                    .json()
                                    .await?
                            }
                        };

                        // Ensure the global state root is the same across iterations.
                        if global_state_root != state_path.global_state_root() {
                            bail!("Inclusion expected the global state root to be the same across iterations")
                        }

                        // Construct the assignment for the state path.
                        let assignment = InclusionAssignment::new(
                            state_path,
                            task.commitment,
                            task.gamma,
                            task.serial_number,
                            local_state_root,
                            !task.is_local,
                        );

                        // Add the assignment to the assignments.
                        assignments.push(assignment);
                    }
                }
                None => bail!("Missing input tasks for transition {} in inclusion", transition.id()),
            }

            // Insert the leaf into the transaction tree.
            transaction_tree.append(&[transaction_leaf.to_bits_le()])?;
        }

        Ok((assignments, global_state_root))
    }

    /// Returns the inclusion assignments for the given fee transition.
    pub async fn prepare_fee_wasm(
        &self,
        fee_transition: &Transition<N>,
        url: &str,
    ) -> Result<Vec<InclusionAssignment<N>>> {
        // Ensure the fee has the correct program ID.
        let fee_program_id = ProgramID::from_str("credits.aleo")?;
        ensure!(*fee_transition.program_id() == fee_program_id, "Incorrect program ID for fee");

        // Ensure the fee has the correct function.
        let fee_function = Identifier::from_str("fee")?;
        ensure!(*fee_transition.function_name() == fee_function, "Incorrect function name for fee");

        // Initialize an empty transaction tree.
        let transaction_tree = N::merkle_tree_bhp::<TRANSACTION_DEPTH>(&[])?;
        // Initialize the global state root.
        let mut global_state_root = N::StateRoot::default();
        // Initialize a vector for the assignments.
        let mut assignments = vec![];

        // Process the input tasks.
        match self.input_tasks.get(fee_transition.id()) {
            Some(tasks) => {
                for task in tasks {
                    // Retrieve the local state root.
                    let local_state_root = (*transaction_tree.root()).into();
                    // Construct the state path.
                    let commitment = &task.commitment;
                    let state_path: StatePath<N> = reqwest::get(&format!("{url}/testnet3/statePath/{commitment}"))
                        .await
                        .map_err(|e| anyhow!("Failed to get state path from the server: {}", e))?
                        .json()
                        .await?;

                    // Ensure the global state root is the same across iterations.
                    if *global_state_root != Field::zero() && global_state_root != state_path.global_state_root() {
                        bail!("Inclusion expected the global state root to be the same across iterations")
                    }

                    // Update the global state root.
                    global_state_root = state_path.global_state_root();

                    // Prepare the assignment for the state path.
                    let assignment = InclusionAssignment::new(
                        state_path,
                        task.commitment,
                        task.gamma,
                        task.serial_number,
                        local_state_root,
                        !task.is_local,
                    );

                    // Add the assignment to the assignments.
                    assignments.push(assignment);
                }
            }
            None => bail!("Missing input state for fee transition {} in inclusion", fee_transition.id()),
        }

        // Ensure the global state root is not zero.
        if *global_state_root == Field::zero() {
            bail!("Inclusion expected the global state root in the fee to *not* be zero")
        }
        // Ensure the assignments are not empty.
        if assignments.is_empty() {
            bail!("Inclusion expected the assignments for the fee to *not* be empty")
        }
        // Return the assignments.
        Ok(assignments)
    }
}
