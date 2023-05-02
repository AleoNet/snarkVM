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

macro_rules! prepare_execution_impl {
    ($self:ident, $execution:ident, $query:ident, $current_state_root:ident, $get_state_path_for_commitment:ident $(, $await:ident)?) => {{
        // Ensure the number of leaves is within the Merkle tree size.
        Transaction::check_execution_size($execution)?;

        // Ensure the proof in the execution is 'None'.
        ensure!($execution.proof().is_none(), "Proof in the execution should not be set yet");

        // Initialize an empty transaction tree.
        let mut transaction_tree = N::merkle_tree_bhp::<TRANSACTION_DEPTH>(&[])?;
        // Initialize a vector for the assignments.
        let mut assignments = vec![];

        // Retrieve the global state root.
        let global_state_root = {
            $query.$current_state_root()
            $(.$await)?
        }?;

        // Ensure the global state root is not zero.
        if *global_state_root == Field::zero() {
            bail!("Inclusion expected the global state root in the execution to *not* be zero")
        }

        for (transition_index, transition) in $execution.transitions().enumerate() {
            // Construct the transaction leaf.
            let transaction_leaf = TransactionLeaf::new_execution(transition_index as u16, **transition.id());

            // Process the input tasks.
            match $self.input_tasks.get(transition.id()) {
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
                                $query.$get_state_path_for_commitment(&task.commitment)
                                $(.$await)?
                            }?
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
    }};
}

impl<N: Network> Inclusion<N> {
    /// Returns the inclusion assignments for the given execution.
    pub fn prepare_execution<B: BlockStorage<N>, Q: Into<Query<N, B>>>(
        &self,
        execution: &Execution<N>,
        query: Q,
    ) -> Result<(Vec<InclusionAssignment<N>>, N::StateRoot)> {
        let query = query.into();
        prepare_execution_impl!(self, execution, query, current_state_root, get_state_path_for_commitment)
    }

    /// Returns the inclusion assignments for the given execution.
    pub async fn prepare_execution_async<B: BlockStorage<N>, Q: Into<Query<N, B>>>(
        &self,
        execution: &Execution<N>,
        query: Q,
    ) -> Result<(Vec<InclusionAssignment<N>>, N::StateRoot)> {
        let query = query.into();
        prepare_execution_impl!(self, execution, query, current_state_root_async, get_state_path_for_commitment_async, await)
    }
}

impl<N: Network> Inclusion<N> {
    /// Checks the inclusion proof for the execution.
    /// Note: This does *not* check that the global state root exists in the ledger.
    pub fn prepare_verify_execution(execution: &Execution<N>) -> Result<(VerifyingKey<N>, Vec<Vec<N::Field>>)> {
        // Retrieve the global state root.
        let global_state_root = execution.global_state_root();

        // Ensure the global state root is not zero.
        if *global_state_root == Field::zero() {
            bail!("Inclusion expected the global state root in the execution to *not* be zero")
        }

        // Initialize an empty transaction tree.
        let mut transaction_tree = N::merkle_tree_bhp::<TRANSACTION_DEPTH>(&[])?;
        // Initialize a vector for the batch verifier inputs.
        let mut batch_verifier_inputs = vec![];

        // Construct the batch verifier inputs.
        for (transition_index, transition) in execution.transitions().enumerate() {
            // Retrieve the local state root.
            let local_state_root = *transaction_tree.root();

            // Iterate through the inputs.
            for input in transition.inputs() {
                // Filter the inputs for records.
                if let Input::Record(serial_number, _) = input {
                    // Add the public inputs to the batch verifier inputs.
                    batch_verifier_inputs.push(vec![
                        N::Field::one(),
                        **global_state_root,
                        *local_state_root,
                        **serial_number,
                    ]);
                }
            }

            // Construct the transaction leaf.
            let transaction_leaf = TransactionLeaf::new_execution(transition_index as u16, **transition.id());
            // Insert the leaf into the transaction tree.
            transaction_tree.append(&[transaction_leaf.to_bits_le()])?;
        }

        // Fetch the inclusion verifying key.
        let verifying_key = VerifyingKey::<N>::new(N::inclusion_verifying_key().clone());
        Ok((verifying_key, batch_verifier_inputs))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_utilities::TestRng;

    #[test]
    fn test_inclusion_verify_execution() {
        let rng = &mut TestRng::default();
        // Fetch an execution transaction.
        let execution_transaction = crate::vm::test_helpers::sample_execution_transaction_with_fee(rng);

        match execution_transaction {
            Transaction::Execute(_, execution, _) => {
                let result = Inclusion::prepare_verify_execution(&execution);
                assert!(result.is_ok());
                let (_vk, inputs) = result.unwrap();
                assert_eq!(inputs.len(), 1);
                // We do not test inclusion individually, as we have tests to batch verify it with transitions elsewhere
            }
            _ => panic!("Expected an execution transaction"),
        }
    }
}
