// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

macro_rules! prepare_execution_impl {
    ($self:ident, $execution:ident, $query:ident, $current_state_root:ident, $get_state_path_for_commitment:ident $(, $await:ident)?) => {{
        // Ensure the number of leaves is within the Merkle tree size.
        Transaction::check_execution_size($execution)?;

        // Ensure the inclusion proof in the execution is 'None'.
        if $execution.inclusion_proof().is_some() {
            bail!("Inclusion proof in the execution should not be set in 'Inclusion::prepare_execution'")
        }

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
    /// Returns a new execution with an inclusion proof, for the given execution.
    pub fn prove_execution<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        execution: Execution<N>,
        assignments: &[InclusionAssignment<N>],
        global_state_root: N::StateRoot,
        rng: &mut R,
    ) -> Result<Execution<N>> {
        match assignments.is_empty() {
            true => {
                // Ensure the global state root is not zero.
                if *global_state_root == Field::zero() {
                    bail!("Inclusion expected the global state root in the execution to *not* be zero")
                }

                // Ensure the inclusion proof in the execution is 'None'.
                if execution.inclusion_proof().is_some() {
                    bail!("Inclusion expected the inclusion proof in the execution to be 'None'")
                }
                // Return the execution.
                Execution::from(execution.into_transitions(), global_state_root, None)
            }
            false => {
                // Fetch the inclusion proving key.
                let proving_key = ProvingKey::<N>::new(N::inclusion_proving_key().clone());

                // Compute the inclusion batch proof.
                let (global_state_root, inclusion_proof) = Self::prove_batch::<A, R>(&proving_key, assignments, rng)?;
                // Return the execution.
                Execution::from(execution.into_transitions(), global_state_root, Some(inclusion_proof))
            }
        }
    }

    /// Checks the inclusion proof for the execution.
    /// Note: This does *not* check that the global state root exists in the ledger.
    pub fn verify_execution(execution: &Execution<N>) -> Result<()> {
        // Retrieve the global state root.
        let global_state_root = execution.global_state_root();

        // Retrieve the inclusion proof.
        let inclusion_proof = execution.inclusion_proof();

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

        // If there are no batch verifier inputs, then ensure the inclusion proof is 'None'.
        if batch_verifier_inputs.is_empty() && inclusion_proof.is_some() {
            bail!("No input records in the execution. Expected the inclusion proof to be 'None'")
        }
        // If there are batch verifier inputs, then ensure the inclusion proof is 'Some'.
        if !batch_verifier_inputs.is_empty() && inclusion_proof.is_none() {
            bail!("Missing inclusion proof for the execution")
        }

        // Verify the inclusion proof.
        if let Some(inclusion_proof) = inclusion_proof {
            // Ensure the global state root is not zero.
            if *global_state_root == Field::zero() {
                bail!("Inclusion expected the global state root in the execution to *not* be zero")
            }

            // Fetch the inclusion verifying key.
            let verifying_key = VerifyingKey::<N>::new(N::inclusion_verifying_key().clone());
            // Verify the inclusion proof.
            ensure!(
                verifying_key.verify_batch(N::INCLUSION_FUNCTION_NAME, &batch_verifier_inputs, inclusion_proof),
                "Inclusion proof is invalid"
            );
        }

        Ok(())
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
                assert!(Inclusion::verify_execution(&execution).is_ok());
            }
            _ => panic!("Expected an execution transaction"),
        }
    }
}
