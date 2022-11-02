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

use crate::{
    BlockStorage,
    BlockStore,
    CallStack,
    Execution,
    Input,
    Operand,
    Output,
    Proof,
    ProvingKey,
    RegisterTypes,
    Stack,
    Transaction,
    Transition,
    VerifyingKey,
};
use console::{
    network::prelude::*,
    program::{
        Entry,
        InputID,
        Literal,
        Plaintext,
        Register,
        StatePath,
        TransactionLeaf,
        TransitionLeaf,
        Value,
        STATE_PATH_FUNCTION_NAME,
        TRANSACTION_DEPTH,
    },
    types::{Address, Field, Group},
};

use std::collections::HashMap;

#[derive(Clone)]
struct InputTask<N: Network> {
    commitment: Field<N>,
    gamma: Group<N>,
    serial_number: Field<N>,
    leaf: TransitionLeaf<N>,
    is_local: bool,
}

#[derive(Clone)]
pub struct Inclusion<N: Network> {
    /// A map of transition IDs to a list of input tasks.
    input_tasks: HashMap<N::TransitionID, Vec<InputTask<N>>>,
    /// A map of commitments to (transition ID, output index) pairs.
    output_commitments: HashMap<Field<N>, (N::TransitionID, u8)>,
}

impl<N: Network> Inclusion<N> {
    pub fn new() -> Self {
        Self { input_tasks: HashMap::new(), output_commitments: HashMap::new() }
    }

    pub fn insert_transition(&mut self, input_ids: &[InputID<N>], transition: &Transition<N>) -> Result<()> {
        // Ensure the transition inputs and input IDs are the same length.
        if input_ids.len() != transition.inputs().len() {
            bail!("Inclusion expected the same number of input IDs as transition inputs")
        }

        for (index, (input, input_id)) in transition.inputs().iter().zip_eq(input_ids).enumerate() {
            // Filter the inputs for records.
            if let InputID::Record(commitment, gamma, serial_number, ..) = input_id {
                // Add the record to the input tasks.
                self.input_tasks.entry(*transition.id()).or_default().push(InputTask {
                    commitment: *commitment,
                    gamma: *gamma,
                    serial_number: *serial_number,
                    leaf: input.to_transition_leaf(index as u8),
                    is_local: self.output_commitments.contains_key(&commitment),
                });
            }
        }

        for (index, output) in transition.outputs().iter().enumerate() {
            // Filter the outputs for records.
            if let Output::Record(commitment, ..) = output {
                // Add the record to the output commitments.
                self.output_commitments.insert(*commitment, (*transition.id(), (input_ids.len() + index) as u8));
            }
        }

        Ok(())
    }

    pub fn prove_batch<A: circuit::Aleo<Network = N>, B: BlockStorage<N>, R: Rng + CryptoRng>(
        &self,
        execution: &Execution<N>,
        block_store: &BlockStore<N, B>,
        rng: &mut R,
    ) -> Result<Execution<N>> {
        // Ensure the number of leaves is within the Merkle tree size.
        Transaction::check_execution_size(execution)?;

        // Initialize an empty transaction tree.
        let mut transaction_tree = N::merkle_tree_bhp::<TRANSACTION_DEPTH>(&[])?;
        // Initialize the global state root.
        let mut global_state_root = N::StateRoot::default();
        // Initialize a vector for the assignments.
        let mut assignments = vec![];

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
                                // Retrieve the global state root.
                                let global_state_root = block_store.current_state_root();
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
                            false => block_store.get_state_path_for_commitment(&task.commitment)?,
                        };

                        // Ensure the global state root is the same across iterations.
                        if *global_state_root != Field::zero() && global_state_root != state_path.global_state_root() {
                            bail!("Inclusion expected the global state root to be the same across iterations")
                        }

                        // Update the global state root.
                        global_state_root = state_path.global_state_root();

                        // Construct the assignment for the state path.
                        let assignment = crate::inject_and_verify_state_path::<N, A>(
                            state_path,
                            task.commitment,
                            task.gamma,
                            task.serial_number,
                            local_state_root,
                            !task.is_local,
                        )?;

                        // Add the assignment to the assignments.
                        assignments.push(assignment);
                    }
                }
                None => bail!("Missing input state for transition {} in inclusion", transition.id()),
            }

            // Insert the leaf into the transaction tree.
            transaction_tree.append(&[transaction_leaf.to_bits_le()])?;
        }

        match assignments.is_empty() {
            true => {
                // Ensure the global state root is zero.
                if *global_state_root != Field::zero() {
                    bail!("Inclusion expected the global state root in the execution to be zero")
                }
                // Ensure the global state root in the execution matches.
                if execution.global_state_root() != global_state_root {
                    bail!("Inclusion expected the global state root in the execution to match")
                }
                // Ensure the inclusion proof in the execution is 'None'.
                if execution.inclusion_proof().is_some() {
                    bail!("Inclusion expected the inclusion proof in the execution to be 'None'")
                }
                // Return the execution.
                Ok(execution.clone())
            }
            false => {
                // Ensure the global state root is not zero.
                if *global_state_root == Field::zero() {
                    bail!("Inclusion expected the global state root in the execution to *not* be zero")
                }
                // Load the inclusion proving key.
                let proving_key = ProvingKey::from_bytes_le(N::state_path_proving_key_bytes())?;
                // Generate the inclusion batch proof.
                let inclusion_proof = proving_key.prove_batch(STATE_PATH_FUNCTION_NAME, &assignments, rng)?;
                // Return the execution.
                Execution::from(execution.into_transitions(), global_state_root, Some(inclusion_proof))
            }
        }
    }

    pub fn verify_batch(execution: &Execution<N>) -> Result<()> {
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

        // Verify the inclusion proof.
        match inclusion_proof {
            Some(inclusion_proof) => {
                // TODO (howardwu): Cache this in the process.
                // Load the inclusion verifying key.
                let verifying_key = VerifyingKey::from_bytes_le(N::state_path_verifying_key_bytes())?;
                // Verify the inclusion proof.
                ensure!(
                    verifying_key.verify_batch(STATE_PATH_FUNCTION_NAME, &batch_verifier_inputs, &inclusion_proof),
                    "Inclusion proof is invalid"
                );
            }
            None => {
                // Ensure the global state root is zero.
                if *global_state_root != Field::<N>::zero() {
                    bail!("Inclusion expected the global state root in the execution to be zero")
                }
            }
        }
        Ok(())
    }
}
