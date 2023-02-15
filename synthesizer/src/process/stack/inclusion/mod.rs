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

use crate::{
    BlockStorage,
    BlockStore,
    Execution,
    Fee,
    Input,
    Output,
    Program,
    Proof,
    ProvingKey,
    Stack,
    Transaction,
    Transition,
    VerifyingKey,
};
use console::{
    network::prelude::*,
    program::{InputID, StatePath, TransactionLeaf, TransitionLeaf, TRANSACTION_DEPTH},
    types::{Field, Group},
};

use console::program::{Identifier, ProgramID};
use std::collections::HashMap;

#[derive(Clone)]
pub enum Query<N: Network, B: BlockStorage<N>> {
    /// The block store from the VM.
    VM(BlockStore<N, B>),
    /// The base URL of the node.
    REST(String),
}

impl<N: Network, B: BlockStorage<N>> From<BlockStore<N, B>> for Query<N, B> {
    fn from(block_store: BlockStore<N, B>) -> Self {
        Self::VM(block_store)
    }
}

impl<N: Network, B: BlockStorage<N>> From<&BlockStore<N, B>> for Query<N, B> {
    fn from(block_store: &BlockStore<N, B>) -> Self {
        Self::VM(block_store.clone())
    }
}

impl<N: Network, B: BlockStorage<N>> From<reqwest::Url> for Query<N, B> {
    fn from(url: reqwest::Url) -> Self {
        Self::REST(url.to_string())
    }
}

impl<N: Network, B: BlockStorage<N>> From<&reqwest::Url> for Query<N, B> {
    fn from(url: &reqwest::Url) -> Self {
        Self::REST(url.to_string())
    }
}

impl<N: Network, B: BlockStorage<N>> From<String> for Query<N, B> {
    fn from(url: String) -> Self {
        Self::REST(url)
    }
}

impl<N: Network, B: BlockStorage<N>> From<&String> for Query<N, B> {
    fn from(url: &String) -> Self {
        Self::REST(url.to_string())
    }
}

impl<N: Network, B: BlockStorage<N>> From<&str> for Query<N, B> {
    fn from(url: &str) -> Self {
        Self::REST(url.to_string())
    }
}

impl<N: Network, B: BlockStorage<N>> Query<N, B> {
    /// Returns the program for the given program ID.
    pub fn get_program(&self, program_id: &ProgramID<N>) -> Result<Program<N>> {
        match self {
            Self::VM(block_store) => {
                block_store.get_program(program_id)?.ok_or_else(|| anyhow!("Program {program_id} not found in storage"))
            }
            #[cfg(not(feature = "wasm"))]
            Self::REST(url) => match N::ID {
                3 => Ok(Self::get_request(&format!("{url}/testnet3/program/{program_id}"))?.json()?),
                _ => bail!("Unsupported network ID in inclusion query"),
            },
            #[cfg(feature = "wasm")]
            _ => bail!("External API calls not supported from WASM"),
        }
    }

    /// Returns the current state root.
    pub fn current_state_root(&self) -> Result<N::StateRoot> {
        match self {
            Self::VM(block_store) => Ok(block_store.current_state_root()),
            #[cfg(not(feature = "wasm"))]
            Self::REST(url) => match N::ID {
                3 => Ok(Self::get_request(&format!("{url}/testnet3/latest/stateRoot"))?.json()?),
                _ => bail!("Unsupported network ID in inclusion query"),
            },
            #[cfg(feature = "wasm")]
            _ => bail!("External API calls not supported from WASM"),
        }
    }

    /// Returns a state path for the given `commitment`.
    pub fn get_state_path_for_commitment(&self, commitment: &Field<N>) -> Result<StatePath<N>> {
        match self {
            Self::VM(block_store) => block_store.get_state_path_for_commitment(commitment),
            #[cfg(not(feature = "wasm"))]
            Self::REST(url) => match N::ID {
                3 => Ok(Self::get_request(&format!("{url}/testnet3/statePath/{commitment}"))?.json()?),
                _ => bail!("Unsupported network ID in inclusion query"),
            },
            #[cfg(feature = "wasm")]
            _ => bail!("External API calls not supported from WASM"),
        }
    }

    /// Performs a GET request to the given URL.
    #[cfg(not(feature = "wasm"))]
    fn get_request(url: &str) -> Result<reqwest::blocking::Response> {
        let response = reqwest::blocking::get(url)?;
        if response.status().is_success() { Ok(response) } else { bail!("Failed to fetch from {}", url) }
    }
}

#[derive(Clone, Debug)]
struct InputTask<N: Network> {
    /// The commitment.
    commitment: Field<N>,
    /// The gamma value.
    gamma: Group<N>,
    /// The serial number.
    serial_number: Field<N>,
    /// The transition leaf.
    leaf: TransitionLeaf<N>,
    /// A boolean indicating whether the input was produced by the current transaction.
    is_local: bool,
}

#[derive(Clone, Debug, Default)]
pub struct Inclusion<N: Network> {
    /// A map of transition IDs to a list of input tasks.
    input_tasks: HashMap<N::TransitionID, Vec<InputTask<N>>>,
    /// A map of commitments to (transition ID, output index) pairs.
    output_commitments: HashMap<Field<N>, (N::TransitionID, u8)>,
}

impl<N: Network> Inclusion<N> {
    /// Initializes a new `Inclusion` instance.
    pub fn new() -> Self {
        Self { input_tasks: HashMap::new(), output_commitments: HashMap::new() }
    }

    /// Inserts the transition to build state for the inclusion proof.
    pub fn insert_transition(&mut self, input_ids: &[InputID<N>], transition: &Transition<N>) -> Result<()> {
        // Ensure the transition inputs and input IDs are the same length.
        if input_ids.len() != transition.inputs().len() {
            bail!("Inclusion expected the same number of input IDs as transition inputs")
        }

        // Initialize the input tasks.
        let input_tasks = self.input_tasks.entry(*transition.id()).or_default();

        // Process the inputs.
        for (index, (input, input_id)) in transition.inputs().iter().zip_eq(input_ids).enumerate() {
            // Filter the inputs for records.
            if let InputID::Record(commitment, gamma, serial_number, ..) = input_id {
                // Add the record to the input tasks.
                input_tasks.push(InputTask {
                    commitment: *commitment,
                    gamma: *gamma,
                    serial_number: *serial_number,
                    leaf: input.to_transition_leaf(index as u8),
                    is_local: self.output_commitments.contains_key(commitment),
                });
            }
        }

        // Process the outputs.
        for (index, output) in transition.outputs().iter().enumerate() {
            // Filter the outputs for records.
            if let Output::Record(commitment, ..) = output {
                // Add the record to the output commitments.
                self.output_commitments.insert(*commitment, (*transition.id(), (input_ids.len() + index) as u8));
            }
        }

        Ok(())
    }

    /// Returns the inclusion assignments for the given execution.
    pub fn prepare_execution<B: BlockStorage<N>, Q: Into<Query<N, B>>>(
        &self,
        execution: &Execution<N>,
        query: Q,
    ) -> Result<(Vec<InclusionAssignment<N>>, N::StateRoot)> {
        let query = query.into();

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
        let global_state_root = query.current_state_root()?;

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
                            false => query.get_state_path_for_commitment(&task.commitment)?,
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

    /// Returns the inclusion assignments for the given fee transition.
    pub fn prepare_fee<B: BlockStorage<N>, Q: Into<Query<N, B>>>(
        &self,
        fee_transition: &Transition<N>,
        query: Q,
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
                let query = query.into();

                for task in tasks {
                    // Retrieve the local state root.
                    let local_state_root = (*transaction_tree.root()).into();
                    // Construct the state path.
                    let state_path = query.get_state_path_for_commitment(&task.commitment)?;

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

    /// Returns a new fee with an inclusion proof, for the given transition.
    pub fn prove_fee<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        fee_transition: Transition<N>,
        assignments: &[InclusionAssignment<N>],
        rng: &mut R,
    ) -> Result<Fee<N>> {
        // Ensure the fee has the correct program ID.
        let fee_program_id = ProgramID::from_str("credits.aleo")?;
        ensure!(*fee_transition.program_id() == fee_program_id, "Incorrect program ID for fee");

        // Ensure the fee has the correct function.
        let fee_function = Identifier::from_str("fee")?;
        ensure!(*fee_transition.function_name() == fee_function, "Incorrect function name for fee");

        // Ensure the assignments are not empty.
        if assignments.is_empty() {
            bail!("Inclusion expected the assignments for the fee to *not* be empty")
        }

        // Fetch the inclusion proving key.
        let proving_key = ProvingKey::<N>::new(N::inclusion_proving_key().clone());

        // Compute the inclusion batch proof.
        let (global_state_root, inclusion_proof) = Self::prove_batch::<A, R>(&proving_key, assignments, rng)?;
        // Return the fee.
        Ok(Fee::from(fee_transition, global_state_root, Some(inclusion_proof)))
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

    /// Checks the inclusion proof for the fee.
    /// Note: This does *not* check that the global state root exists in the ledger.
    pub fn verify_fee(fee: &Fee<N>) -> Result<()> {
        // Retrieve the global state root.
        let global_state_root = fee.global_state_root();
        // Ensure the global state root is not zero.
        if *global_state_root == Field::zero() {
            bail!("Inclusion expected the global state root in the fee to *not* be zero")
        }

        // Retrieve the inclusion proof.
        let inclusion_proof = match fee.inclusion_proof() {
            Some(inclusion_proof) => inclusion_proof,
            None => bail!("Inclusion expected the fee to contain an inclusion proof"),
        };

        // Initialize an empty transaction tree.
        let transaction_tree = N::merkle_tree_bhp::<TRANSACTION_DEPTH>(&[])?;
        // Initialize a vector for the batch verifier inputs.
        let mut batch_verifier_inputs = vec![];

        // Retrieve the local state root.
        let local_state_root = *transaction_tree.root();

        // Construct the batch verifier inputs.
        for input in fee.inputs() {
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

        // Ensure there are batch verifier inputs.
        if batch_verifier_inputs.is_empty() {
            bail!("Inclusion expected the fee to contain input records")
        }

        // Fetch the inclusion verifying key.
        let verifying_key = VerifyingKey::<N>::new(N::inclusion_verifying_key().clone());
        // Verify the inclusion proof.
        ensure!(
            verifying_key.verify_batch(N::INCLUSION_FUNCTION_NAME, &batch_verifier_inputs, inclusion_proof),
            "Inclusion proof is invalid"
        );

        Ok(())
    }

    /// Returns the global state root and inclusion proof for the given assignments.
    fn prove_batch<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        proving_key: &ProvingKey<N>,
        assignments: &[InclusionAssignment<N>],
        rng: &mut R,
    ) -> Result<(N::StateRoot, Proof<N>)> {
        // Initialize the global state root.
        let mut global_state_root = N::StateRoot::default();
        // Initialize a vector for the batch assignments.
        let mut batch_assignments = vec![];

        for assignment in assignments.iter() {
            // Ensure the global state root is the same across iterations.
            if *global_state_root != Field::zero() && global_state_root != assignment.state_path.global_state_root() {
                bail!("Inclusion expected the global state root to be the same across iterations")
            }
            // Update the global state root.
            global_state_root = assignment.state_path.global_state_root();

            // Add the assignment to the assignments.
            batch_assignments.push(assignment.to_circuit_assignment::<A>()?);
        }

        // Ensure the global state root is not zero.
        if *global_state_root == Field::zero() {
            bail!("Inclusion expected the global state root in the execution to *not* be zero")
        }

        // Generate the inclusion batch proof.
        let inclusion_proof = proving_key.prove_batch(N::INCLUSION_FUNCTION_NAME, &batch_assignments, rng)?;
        // Return the global state root and inclusion proof.
        Ok((global_state_root, inclusion_proof))
    }
}

pub struct InclusionAssignment<N: Network> {
    state_path: StatePath<N>,
    commitment: Field<N>,
    gamma: Group<N>,
    serial_number: Field<N>,
    local_state_root: N::TransactionID,
    is_global: bool,
}

impl<N: Network> InclusionAssignment<N> {
    /// Initializes a new inclusion assignment.
    pub fn new(
        state_path: StatePath<N>,
        commitment: Field<N>,
        gamma: Group<N>,
        serial_number: Field<N>,
        local_state_root: N::TransactionID,
        is_global: bool,
    ) -> Self {
        Self { state_path, commitment, gamma, serial_number, local_state_root, is_global }
    }

    /// The circuit for state path verification.
    ///
    /// # Diagram
    /// The `[[ ]]` notation is used to denote public inputs.
    /// ```ignore
    ///             [[ global_state_root ]] || [[ local_state_root ]]
    ///                        |                          |
    ///                        -------- is_global --------
    ///                                     |
    ///                                state_path
    ///                                    |
    /// [[ serial_number ]] := Commit( commitment || Hash( COFACTOR * gamma ) )
    /// ```
    pub fn to_circuit_assignment<A: circuit::Aleo<Network = N>>(&self) -> Result<circuit::Assignment<N::Field>> {
        use circuit::Inject;

        // Ensure the circuit environment is clean.
        assert_eq!(A::count(), (0, 1, 0, 0, 0));
        A::reset();

        // Inject the state path as `Mode::Private` (with a global state root as `Mode::Public`).
        let state_path = circuit::StatePath::<A>::new(circuit::Mode::Private, self.state_path.clone());
        // Inject the commitment as `Mode::Private`.
        let commitment = circuit::Field::<A>::new(circuit::Mode::Private, self.commitment);
        // Inject the gamma as `Mode::Private`.
        let gamma = circuit::Group::<A>::new(circuit::Mode::Private, self.gamma);

        // Inject the local state root as `Mode::Public`.
        let local_state_root = circuit::Field::<A>::new(circuit::Mode::Public, *self.local_state_root);
        // Inject the 'is_global' flag as `Mode::Private`.
        let is_global = circuit::Boolean::<A>::new(circuit::Mode::Private, self.is_global);

        // Inject the serial number as `Mode::Public`.
        let serial_number = circuit::Field::<A>::new(circuit::Mode::Public, self.serial_number);
        // Compute the candidate serial number.
        let candidate_serial_number =
            circuit::Record::<A, circuit::Plaintext<A>>::serial_number_from_gamma(&gamma, commitment.clone());
        // Enforce that the candidate serial number is equal to the serial number.
        A::assert_eq(&candidate_serial_number, &serial_number);

        // Enforce the starting leaf is the claimed commitment.
        A::assert_eq(state_path.transition_leaf().id(), commitment);
        // Enforce the state path from leaf to root is correct.
        A::assert(state_path.verify(&is_global, &local_state_root));

        #[cfg(debug_assertions)]
        Stack::log_circuit::<A, _>(&format!("State Path for {}", self.serial_number));

        // Eject the assignment and reset the circuit environment.
        Ok(A::eject_assignment_and_reset())
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
        let execution_transaction = crate::vm::test_helpers::sample_execution_transaction(rng);

        match execution_transaction {
            Transaction::Execute(_, execution, _) => {
                assert!(Inclusion::verify_execution(&execution).is_ok());
            }
            _ => panic!("Expected an execution transaction"),
        }
    }

    #[test]
    fn test_inclusion_verify_fee() {
        let rng = &mut TestRng::default();
        // Fetch a deployment transaction.
        let deployment_transaction = crate::vm::test_helpers::sample_deployment_transaction(rng);

        match deployment_transaction {
            Transaction::Deploy(_, _, fee) => {
                assert!(Inclusion::verify_fee(&fee).is_ok());
            }
            _ => panic!("Expected a deployment transaction"),
        }
    }
}
