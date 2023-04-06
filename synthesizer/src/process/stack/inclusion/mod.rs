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
    program::{Identifier, InputID, ProgramID, StatePath, TransactionLeaf, TransitionLeaf, TRANSACTION_DEPTH},
    types::{Field, Group},
};

use std::collections::HashMap;

#[derive(Clone)]
pub enum Query<N: Network, B: BlockStorage<N>> {
    /// Block store from the VM to search for inclusion proof data
    VM(BlockStore<N, B>),
    /// Base URL of the node to fetch inclusion proof data
    REST(String),
    /// Inclusion proof data fetched from an outside environment
    LOCAL(N::StateRoot, HashMap<Field<N>, StatePath<N>>),
}

impl<N: Network, B: BlockStorage<N>> TryFrom<(&str, &str)> for Query<N, B> {
    type Error = anyhow::Error;

    fn try_from(inclusion_data: (&str, &str)) -> std::result::Result<Self, Self::Error> {
        let (state_root, commitment_map) = inclusion_data;
        Ok(Self::LOCAL(
            N::StateRoot::from_str(state_root).map_err(|_| anyhow!("Invalid state root"))?,
            serde_json::from_str(commitment_map).map_err(|_| anyhow!("Invalid state path"))?,
        ))
    }
}

impl<N: Network, B: BlockStorage<N>> From<(N::StateRoot, HashMap<Field<N>, StatePath<N>>)> for Query<N, B> {
    fn from(inclusion_data: (N::StateRoot, HashMap<Field<N>, StatePath<N>>)) -> Self {
        let (state_root, commitments) = inclusion_data;
        Self::LOCAL(state_root, commitments)
    }
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
                3 => Ok(Self::get_request(&format!("{url}/testnet3/program/{program_id}"))?.into_json()?),
                _ => bail!("Unsupported network ID in inclusion query"),
            },
            _ => bail!("Program queries not supported in offline environments"),
        }
    }

    /// Returns the current state root.
    pub fn current_state_root(&self) -> Result<N::StateRoot> {
        match self {
            Self::VM(block_store) => Ok(block_store.current_state_root()),
            #[cfg(not(feature = "wasm"))]
            Self::REST(url) => match N::ID {
                3 => Ok(Self::get_request(&format!("{url}/testnet3/latest/stateRoot"))?.into_json()?),
                _ => bail!("Unsupported network ID in inclusion query"),
            },
            Self::LOCAL(state_root, _) => Ok(*state_root),
            #[cfg(feature = "wasm")]
            _ => bail!("REST queries not supported in wasm environments"),
        }
    }

    /// Returns a state path for the given `commitment`.
    pub fn get_state_path_for_commitment(&self, commitment: &Field<N>) -> Result<StatePath<N>> {
        match self {
            Self::VM(block_store) => block_store.get_state_path_for_commitment(commitment),
            #[cfg(not(feature = "wasm"))]
            Self::REST(url) => match N::ID {
                3 => Ok(Self::get_request(&format!("{url}/testnet3/statePath/{commitment}"))?.into_json()?),
                _ => bail!("Unsupported network ID in inclusion query"),
            },
            Self::LOCAL(_, commitments) => {
                let state_path =
                    commitments.get(commitment).ok_or_else(|| anyhow!("Commitment not found in inclusion query"))?;
                Ok(state_path.clone())
            }
            #[cfg(feature = "wasm")]
            _ => bail!("REST queries not supported in wasm environments"),
        }
    }

    /// Performs a GET request to the given URL.
    #[cfg(not(feature = "wasm"))]
    fn get_request(url: &str) -> Result<ureq::Response> {
        let response = ureq::get(url).call()?;
        if response.status() == 200 { Ok(response) } else { bail!("Failed to fetch from {}", url) }
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
        proving_key: Option<ProvingKey<N>>,
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
                let proving_key =
                    proving_key.unwrap_or_else(|| ProvingKey::<N>::new(N::inclusion_proving_key().clone()));
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
        proving_key: Option<ProvingKey<N>>,
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
        let proving_key = proving_key.unwrap_or_else(|| ProvingKey::<N>::new(N::inclusion_proving_key().clone()));

        // Compute the inclusion batch proof.
        let (global_state_root, inclusion_proof) = Self::prove_batch::<A, R>(&proving_key, assignments, rng)?;
        // Return the fee.
        Ok(Fee::from(fee_transition, global_state_root, Some(inclusion_proof)))
    }

    /// Checks the inclusion proof for the execution.
    /// Note: This does *not* check that the global state root exists in the ledger.
    pub fn verify_execution(execution: &Execution<N>, verifying_key: Option<VerifyingKey<N>>) -> Result<()> {
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
            let verifying_key =
                verifying_key.unwrap_or_else(|| VerifyingKey::<N>::new(N::inclusion_verifying_key().clone()));
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
    pub fn verify_fee(fee: &Fee<N>, verifying_key: Option<VerifyingKey<N>>) -> Result<()> {
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
        let verifying_key =
            verifying_key.unwrap_or_else(|| VerifyingKey::<N>::new(N::inclusion_verifying_key().clone()));
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
    use crate::{
        cast_ref,
        vm::test_helpers::{sample_deployment_transaction, sample_execution_transaction},
        Authorization,
        BlockMemory,
        CallMetrics,
        Process,
    };
    use console::{
        account::PrivateKey,
        program::{Response, Value},
    };
    use snarkvm_utilities::TestRng;

    type CurrentNetwork = console::network::Testnet3;
    type CurrentAleo = circuit::network::AleoV0;
    const COMMITMENT: &str = r"4874757399230654999279876063378939895075480265760505926730283954993786291609field";
    const COMMITMENT_MAP: &str = r#"{"4874757399230654999279876063378939895075480265760505926730283954993786291609field": "path1qqqzcvgx7n7y4sgjyzdkdlhn7ew4gydwshtlty84hul59jk3zyqvuzfkqqqqqqqqqqq2nxkl6lnue70g7khz72x76f3np35mkdkjvczz5ya3d4lf7fnx7plr64ptwy0wz4xe6sex2aw3hpunh8vnz6ce4rsnjf333k0vqn3lpx5exr9auj7lx536yxrn0zy54tu5e38kmgyvmfqj2shuksx7jvepy6u3998xzrgmd59hy9pz75p6l683jhjg2p95gly0x8v523ker8qzhva8uy3tas82wwa7ymzwr92ysn2w7lm3r3tdm45wfwve6ssqruppfq0sn69ud8a2c554tnazt3trper5h02yufw8r45r7x6l2293vragtjlkeacu0nuqhpuw4wmclwplzg9ruecw3mavaans537jd44qp6tvwxpffjnlzzg924uaf8snpat4ve95mzl4u9nlxc09unpsuqjqjr8ygw29xdhsc2h5sdvgh0d8lw3ex0tas8m7jd0mme4vagtw6psqm2nurmm8kd28hp4k2r7xatvrw7rw7qghc0wmn0mrqvs8wx2wf59d7x6vtav05l6z8lp3xvdcfkyd90ztluda6nrnm7pp3lny8dvlzzvfmfmh5tvlsdrvldn2fd3hqsvrndm5vm3curxq8amx3kazcvgaz2zpt849p28f5rjv3za44u8c9ddny3lm2svj3fnrqr0uy7skg4dqfpq4n6js4r56pexg3w667ruzkkejgla4gxfg5e3sph7z0gty2ksyss2eafg236dqunyghdd0p7pttvey0765ry52vccqmlp859j9tgzgg9v7559gaxswfjytkkhslq44kvj8ld2pj29xvvqdlsn6zez45pyyzk022z5wng8yez9mttc0s26mxfrlk4qe9znxxqxlcfapv326qjzpt849p28f5rjv3za44u8c9ddny3lm2svj3fnrqr0uy7skg4dqfpq4n6js4r56pexg3w667ruzkkejgla4gxfg5e3sph7z0gty2ksyss2eafg236dqunyghdd0p7pttvey0765ry52vccqmlp859j9tgzgg9v7559gaxswfjytkkhslq44kvj8ld2pj29xvvqdlsn6zez45pyyzk022z5wng8yez9mttc0s26mxfrlk4qe9znxxqxlcfapv326qjzpt849p28f5rjv3za44u8c9ddny3lm2svj3fnrqr0uy7skg4dqfpq4n6js4r56pexg3w667ruzkkejgla4gxfg5e3sph7z0gty2ksyss2eafg236dqunyghdd0p7pttvey0765ry52vccqmlp859j9tgzgg9v7559gaxswfjytkkhslq44kvj8ld2pj29xvvqdlsn6zez45pyyzk022z5wng8yez9mttc0s26mxfrlk4qe9znxxqxlcfapv326qjzpt849p28f5rjv3za44u8c9ddny3lm2svj3fnrqr0uy7skg4dqfpq4n6js4r56pexg3w667ruzkkejgla4gxfg5e3sph7z0gty2ksyss2eafg236dqunyghdd0p7pttvey0765ry52vccqmlp859j9tgzgg9v7559gaxswfjytkkhslq44kvj8ld2pj29xvvqdlsn6zez45pyyzk022z5wng8yez9mttc0s26mxfrlk4qe9znxxqxlcfapv326qj8hdgqzvtea2t4ry8hnc4d63th6y29tdvjta48rtpxkl8zfej5qmjj5ayyy7ac22w79ttzztuhyvf3zna90hl70t54nk9ala3499qsvx954sr3e6dek8v6dd4mrxayyah6u7cdvwqvapnvs2dye8y8wcvgszqqqqqqqqqqqm55t50ma732h5s9s785pxrkdz5c9xdm3t5vd9xxqyqvdjg93wyfx8ce6fm5jhhfup3as6eg7m95h7hhd38f2m2e8w582lwzj253rkp8742hl94rvs9qas6ef6r4mxt4ssdswwykh9rhr79gexf3wrsprqqq65qzm6ea2vduhs450n0dzp9da07dr4ndfhxktacv98h500v9xjqcqqqqqqqqqqqqgg9v7559gaxswfjytkkhslq44kvj8ld2pj29xvvqdlsn6zez45pyyzk022z5wng8yez9mttc0s26mxfrlk4qe9znxxqxlcfapv326qjzpt849p28f5rjv3za44u8c9ddny3lm2svj3fnrqr0uy7skg4dqfpq4n6js4r56pexg3w667ruzkkejgla4gxfg5e3sph7z0gty2ksyss2eafg236dqunyghdd0p7pttvey0765ry52vccqmlp859j9tgzgg9v7559gaxswfjytkkhslq44kvj8ld2pj29xvvqdlsn6zez45pyyzk022z5wng8yez9mttc0s26mxfrlk4qe9znxxqxlcfapv326qjzpt849p28f5rjv3za44u8c9ddny3lm2svj3fnrqr0uy7skg4dqfpq4n6js4r56pexg3w667ruzkkejgla4gxfg5e3sph7z0gty2ksyss2eafg236dqunyghdd0p7pttvey0765ry52vccqmlp859j9tgzgg9v7559gaxswfjytkkhslq44kvj8ld2pj29xvvqdlsn6zez45pyyzk022z5wng8yez9mttc0s26mxfrlk4qe9znxxqxlcfapv326qjzpt849p28f5rjv3za44u8c9ddny3lm2svj3fnrqr0uy7skg4dqfpq4n6js4r56pexg3w667ruzkkejgla4gxfg5e3sph7z0gty2ksyss2eafg236dqunyghdd0p7pttvey0765ry52vccqmlp859j9tgzgg9v7559gaxswfjytkkhslq44kvj8ld2pj29xvvqdlsn6zez45pqjr4zcfvlxmmrnv535p5fyje2qt6muy3rzr3mya4pu543cv5m0qcqqqqqqqqqqqqyyzk022z5wng8yez9mttc0s26mxfrlk4qe9znxxqxlcfapv326qjzpt849p28f5rjv3za44u8c9ddny3lm2svj3fnrqr0uy7skg4dqfpq4n6js4r56pexg3w667ruzkkejgla4gxfg5e3sph7z0gty2ksyss2eafg236dqunyghdd0p7pttvey0765ry52vccqmlp859j9tgzqzqqqdzndt6u5ra2x52ze36ahgggzz2mfnh45lsw9cpu3qc9ea72n9yxsxqqqqqqqqqqq0rryangqmqe4m0ecrjxrp20yy2xfm4n9ww5r0a9kvpdg2d5rq5r3zm3zks4dspjw6d69fzta9rsekv5jluwg7ajpcj2sate23xngjrkw5uhg30e6ufy3r03p69y900vselx9ah7ra9tcv0gyua9m5s32p6zpt849p28f5rjv3za44u8c9ddny3lm2svj3fnrqr0uy7skg4dqgqqrqvqfnpdu9wtdcfu6c3ke43e3cjxy3h5rr75h44l3qyddmz2g6ypuwzsfapyfp"}"#;
    const STATE_PATH: &str = r"path1qqqzcvgx7n7y4sgjyzdkdlhn7ew4gydwshtlty84hul59jk3zyqvuzfkqqqqqqqqqqq2nxkl6lnue70g7khz72x76f3np35mkdkjvczz5ya3d4lf7fnx7plr64ptwy0wz4xe6sex2aw3hpunh8vnz6ce4rsnjf333k0vqn3lpx5exr9auj7lx536yxrn0zy54tu5e38kmgyvmfqj2shuksx7jvepy6u3998xzrgmd59hy9pz75p6l683jhjg2p95gly0x8v523ker8qzhva8uy3tas82wwa7ymzwr92ysn2w7lm3r3tdm45wfwve6ssqruppfq0sn69ud8a2c554tnazt3trper5h02yufw8r45r7x6l2293vragtjlkeacu0nuqhpuw4wmclwplzg9ruecw3mavaans537jd44qp6tvwxpffjnlzzg924uaf8snpat4ve95mzl4u9nlxc09unpsuqjqjr8ygw29xdhsc2h5sdvgh0d8lw3ex0tas8m7jd0mme4vagtw6psqm2nurmm8kd28hp4k2r7xatvrw7rw7qghc0wmn0mrqvs8wx2wf59d7x6vtav05l6z8lp3xvdcfkyd90ztluda6nrnm7pp3lny8dvlzzvfmfmh5tvlsdrvldn2fd3hqsvrndm5vm3curxq8amx3kazcvgaz2zpt849p28f5rjv3za44u8c9ddny3lm2svj3fnrqr0uy7skg4dqfpq4n6js4r56pexg3w667ruzkkejgla4gxfg5e3sph7z0gty2ksyss2eafg236dqunyghdd0p7pttvey0765ry52vccqmlp859j9tgzgg9v7559gaxswfjytkkhslq44kvj8ld2pj29xvvqdlsn6zez45pyyzk022z5wng8yez9mttc0s26mxfrlk4qe9znxxqxlcfapv326qjzpt849p28f5rjv3za44u8c9ddny3lm2svj3fnrqr0uy7skg4dqfpq4n6js4r56pexg3w667ruzkkejgla4gxfg5e3sph7z0gty2ksyss2eafg236dqunyghdd0p7pttvey0765ry52vccqmlp859j9tgzgg9v7559gaxswfjytkkhslq44kvj8ld2pj29xvvqdlsn6zez45pyyzk022z5wng8yez9mttc0s26mxfrlk4qe9znxxqxlcfapv326qjzpt849p28f5rjv3za44u8c9ddny3lm2svj3fnrqr0uy7skg4dqfpq4n6js4r56pexg3w667ruzkkejgla4gxfg5e3sph7z0gty2ksyss2eafg236dqunyghdd0p7pttvey0765ry52vccqmlp859j9tgzgg9v7559gaxswfjytkkhslq44kvj8ld2pj29xvvqdlsn6zez45pyyzk022z5wng8yez9mttc0s26mxfrlk4qe9znxxqxlcfapv326qjzpt849p28f5rjv3za44u8c9ddny3lm2svj3fnrqr0uy7skg4dqfpq4n6js4r56pexg3w667ruzkkejgla4gxfg5e3sph7z0gty2ksyss2eafg236dqunyghdd0p7pttvey0765ry52vccqmlp859j9tgzgg9v7559gaxswfjytkkhslq44kvj8ld2pj29xvvqdlsn6zez45pyyzk022z5wng8yez9mttc0s26mxfrlk4qe9znxxqxlcfapv326qj8hdgqzvtea2t4ry8hnc4d63th6y29tdvjta48rtpxkl8zfej5qmjj5ayyy7ac22w79ttzztuhyvf3zna90hl70t54nk9ala3499qsvx954sr3e6dek8v6dd4mrxayyah6u7cdvwqvapnvs2dye8y8wcvgszqqqqqqqqqqqm55t50ma732h5s9s785pxrkdz5c9xdm3t5vd9xxqyqvdjg93wyfx8ce6fm5jhhfup3as6eg7m95h7hhd38f2m2e8w582lwzj253rkp8742hl94rvs9qas6ef6r4mxt4ssdswwykh9rhr79gexf3wrsprqqq65qzm6ea2vduhs450n0dzp9da07dr4ndfhxktacv98h500v9xjqcqqqqqqqqqqqqgg9v7559gaxswfjytkkhslq44kvj8ld2pj29xvvqdlsn6zez45pyyzk022z5wng8yez9mttc0s26mxfrlk4qe9znxxqxlcfapv326qjzpt849p28f5rjv3za44u8c9ddny3lm2svj3fnrqr0uy7skg4dqfpq4n6js4r56pexg3w667ruzkkejgla4gxfg5e3sph7z0gty2ksyss2eafg236dqunyghdd0p7pttvey0765ry52vccqmlp859j9tgzgg9v7559gaxswfjytkkhslq44kvj8ld2pj29xvvqdlsn6zez45pyyzk022z5wng8yez9mttc0s26mxfrlk4qe9znxxqxlcfapv326qjzpt849p28f5rjv3za44u8c9ddny3lm2svj3fnrqr0uy7skg4dqfpq4n6js4r56pexg3w667ruzkkejgla4gxfg5e3sph7z0gty2ksyss2eafg236dqunyghdd0p7pttvey0765ry52vccqmlp859j9tgzgg9v7559gaxswfjytkkhslq44kvj8ld2pj29xvvqdlsn6zez45pyyzk022z5wng8yez9mttc0s26mxfrlk4qe9znxxqxlcfapv326qjzpt849p28f5rjv3za44u8c9ddny3lm2svj3fnrqr0uy7skg4dqfpq4n6js4r56pexg3w667ruzkkejgla4gxfg5e3sph7z0gty2ksyss2eafg236dqunyghdd0p7pttvey0765ry52vccqmlp859j9tgzgg9v7559gaxswfjytkkhslq44kvj8ld2pj29xvvqdlsn6zez45pqjr4zcfvlxmmrnv535p5fyje2qt6muy3rzr3mya4pu543cv5m0qcqqqqqqqqqqqqyyzk022z5wng8yez9mttc0s26mxfrlk4qe9znxxqxlcfapv326qjzpt849p28f5rjv3za44u8c9ddny3lm2svj3fnrqr0uy7skg4dqfpq4n6js4r56pexg3w667ruzkkejgla4gxfg5e3sph7z0gty2ksyss2eafg236dqunyghdd0p7pttvey0765ry52vccqmlp859j9tgzqzqqqdzndt6u5ra2x52ze36ahgggzz2mfnh45lsw9cpu3qc9ea72n9yxsxqqqqqqqqqqq0rryangqmqe4m0ecrjxrp20yy2xfm4n9ww5r0a9kvpdg2d5rq5r3zm3zks4dspjw6d69fzta9rsekv5jluwg7ajpcj2sate23xngjrkw5uhg30e6ufy3r03p69y900vselx9ah7ra9tcv0gyua9m5s32p6zpt849p28f5rjv3za44u8c9ddny3lm2svj3fnrqr0uy7skg4dqgqqrqvqfnpdu9wtdcfu6c3ke43e3cjxy3h5rr75h44l3qyddmz2g6ypuwzsfapyfp";
    const STATE_ROOT: &str = r"ar19scsda8uftq3ygymvml08aja2sg6apwh7kg0t0elgt9dzygqecys8m9c4g";

    #[test]
    fn test_inclusion_verify_execution() {
        let rng = &mut TestRng::default();
        // Fetch an execution transaction.
        let execution_transaction = sample_execution_transaction(rng);

        // Get verifying key as if it were being passed in from an external context.
        let verifying_key = VerifyingKey::<CurrentNetwork>::new(CurrentNetwork::inclusion_verifying_key().clone());

        match execution_transaction {
            Transaction::Execute(_, execution, _) => {
                // Assert stateful verification passes.
                assert!(Inclusion::verify_execution(&execution, None).is_ok());

                // Assert stateless verification passes.
                assert!(Inclusion::verify_execution(&execution, Some(verifying_key)).is_ok());
            }
            _ => panic!("Expected an execution transaction"),
        }
    }

    #[test]
    fn test_inclusion_verify_fee() {
        let rng = &mut TestRng::default();
        // Fetch a deployment transaction.
        let deployment_transaction = sample_deployment_transaction(rng);

        // Get verifying key as if it were being passed in from an external context.
        let verifying_key = VerifyingKey::<CurrentNetwork>::new(CurrentNetwork::inclusion_verifying_key().clone());

        match deployment_transaction {
            Transaction::Deploy(_, _, fee) => {
                // Assert stateful verification passes.
                assert!(Inclusion::verify_fee(&fee, None).is_ok());

                // Assert stateless verification passes.
                assert!(Inclusion::verify_fee(&fee, Some(verifying_key)).is_ok());
            }
            _ => panic!("Expected a deployment transaction"),
        }
    }

    #[test]
    fn test_local_query_variant_serialization() {
        // Commitments and state roots fetched from testnet3 api
        let program_id = ProgramID::<CurrentNetwork>::from_str("hello.aleo").unwrap();

        // Convert the state root to a field element
        let commitment = Field::<CurrentNetwork>::from_str(COMMITMENT).unwrap();
        let commitment_map: HashMap<Field<CurrentNetwork>, StatePath<CurrentNetwork>> =
            serde_json::from_str(COMMITMENT_MAP).unwrap();
        let state_root = <CurrentNetwork as Network>::StateRoot::from_str(STATE_ROOT).unwrap();
        let state_path = StatePath::<CurrentNetwork>::from_str(STATE_PATH).unwrap();

        // Ensure queries can be constructed from both structs and strings
        let query_from_struct =
            Query::<CurrentNetwork, BlockMemory<CurrentNetwork>>::from((state_root, commitment_map));
        let query_from_str =
            Query::<CurrentNetwork, BlockMemory<CurrentNetwork>>::try_from((STATE_ROOT, COMMITMENT_MAP)).unwrap();

        // Ensure associated methods return the correct values
        assert_eq!(query_from_struct.get_state_path_for_commitment(&commitment).unwrap(), state_path);
        assert_eq!(query_from_str.get_state_path_for_commitment(&commitment).unwrap(), state_path);
        assert_eq!(query_from_struct.current_state_root().unwrap(), state_root);
        assert_eq!(query_from_str.current_state_root().unwrap(), state_root);
        assert!(query_from_struct.get_program(&program_id).is_err());
        assert!(query_from_str.get_program(&program_id).is_err());
    }

    #[test]
    fn test_wasm_execution_flow_with_inclusion_proof() {
        // Test an inclusion proof in the way it would be done in webassembly context.

        //----------- DATA ASSUMED TO BE SUPPLIED BY THE PROVER FROM OUTSIDE WASM -----------
        let inclusion_proving_key = ProvingKey::<CurrentNetwork>::new(CurrentNetwork::inclusion_proving_key().clone());
        let inclusion_verifying_key =
            VerifyingKey::<CurrentNetwork>::new(CurrentNetwork::inclusion_verifying_key().clone());
        let credits_proving_key = ProvingKey::<CurrentNetwork>::new(
            CurrentNetwork::get_credits_proving_key("transfer".to_string()).unwrap().clone(),
        );

        // Initialize a new caller account.
        let caller_private_key =
            PrivateKey::from_str("APrivateKey1zkpJNtSFD3LfsSHhuUgUVfdtHqSrm2wjWLRqUkHALUBw4Lb").unwrap();

        let record_string = r"{owner: aleo1f3wd9pvw2z9mrwl9s6v7c0tdp4yw4et0304ltq6lp65d45x095psmj9wd4.private,  gates: 50200000u64.private,  _nonce: 3456560291181264315715430728275848162867086452732010598924408047526149762526group.public}";
        let r0 = Value::<CurrentNetwork>::from_str(record_string).unwrap();
        let r1 = Value::<CurrentNetwork>::from_str(r"aleo1f3wd9pvw2z9mrwl9s6v7c0tdp4yw4et0304ltq6lp65d45x095psmj9wd4")
            .unwrap();
        let r2 = Value::<CurrentNetwork>::from_str("50000u64").unwrap();

        //----------- FUNCTIONS ASSUMED TO BE COMPILED INTO WEBASSEMBLY -----------
        // Create an authorization for the given function & get input commitments needed to find state-paths
        fn authorize_offline(
            caller_private_key: &PrivateKey<CurrentNetwork>,
            program_id: impl TryInto<ProgramID<CurrentNetwork>>,
            function_name: impl TryInto<Identifier<CurrentNetwork>>,
            inputs: impl ExactSizeIterator<Item = impl TryInto<Value<CurrentNetwork>>>,
        ) -> Result<(Authorization<CurrentNetwork>, Vec<Field<CurrentNetwork>>)> {
            let rng = &mut TestRng::default();
            let process = Process::<CurrentNetwork>::load_offline()?;
            let authorization =
                process.authorize::<CurrentAleo, _>(caller_private_key, program_id, function_name, inputs, rng)?;
            let commitments = authorization
                .to_vec_deque()
                .iter()
                .flat_map(|request| request.input_ids())
                .filter_map(|input| if let InputID::Record(commitment, ..) = input { Some(*commitment) } else { None })
                .collect();
            Ok((authorization, commitments))
        }

        // Execute a program with necessary data inserted from external environment
        fn execute_program(
            program_id: &str,
            function_name: &str,
            authorization: Authorization<CurrentNetwork>,
            state_root: &str,
            commitment_map: &str,
            program_proving_key: ProvingKey<CurrentNetwork>,
            inclusion_proving_key: ProvingKey<CurrentNetwork>,
        ) -> Result<(
            Response<CurrentNetwork>,
            Execution<CurrentNetwork>,
            Inclusion<CurrentNetwork>,
            Vec<CallMetrics<CurrentNetwork>>,
        )> {
            let rng = &mut TestRng::default();
            let program_id = ProgramID::<CurrentNetwork>::from_str(program_id)?;
            let function_name = Identifier::<CurrentNetwork>::from_str(function_name)?;

            // Load the process
            let process = Process::<CurrentNetwork>::load_offline()?;
            process.insert_proving_key(&program_id, &function_name, program_proving_key)?;

            // Execute the call.
            let (response, execution, inclusion, metrics) = process.execute::<CurrentAleo, _>(authorization, rng)?;

            let query = Query::<CurrentNetwork, BlockMemory<CurrentNetwork>>::try_from((state_root, commitment_map))?;
            // Prepare the assignments.
            let (assignments, global_state_root) = {
                let execution = cast_ref!(execution as Execution<CurrentNetwork>);
                let inclusion = cast_ref!(inclusion as Inclusion<CurrentNetwork>);
                inclusion.prepare_execution(execution, query)?
            };
            let assignments = cast_ref!(assignments as Vec<InclusionAssignment<CurrentNetwork>>);
            let global_state_root = *cast_ref!((*global_state_root) as Field<CurrentNetwork>);

            // Compute the inclusion proof and update the execution.
            let execution = inclusion.prove_execution::<CurrentAleo, _>(
                execution,
                assignments,
                global_state_root.into(),
                Some(inclusion_proving_key),
                rng,
            )?;

            // Prepare the return.
            let response = cast_ref!(response as Response<CurrentNetwork>).clone();
            let execution = cast_ref!(execution as Execution<CurrentNetwork>).clone();
            let metrics = cast_ref!(metrics as Vec<CallMetrics<CurrentNetwork>>).clone();

            // Return the response, execution, and metrics.
            Ok((response, execution, inclusion, metrics))
        }

        //----------- FUNCTIONS ASSUMED TO BE EXECUTED OUTSIDE OF WEBASSEMBLY -----------
        // This function would be non-wasm function (most likely in javascript that takes the
        // "commitments" output from get_authorization_offline and use it to make a call in
        // the outside environment to the Aleo API to get the state roots and state paths
        fn get_inclusion_proof_data(_commitments: &[Field<CurrentNetwork>]) -> (&str, &str) {
            (STATE_ROOT, COMMITMENT_MAP)
        }

        //----------- SAMPLE WEB PROVING PROGRAM FLOW -----------
        // This program execution flow would be executed from javascript

        // ENTER WASM: Get authorization and commitments
        let (authorization, commitments) =
            authorize_offline(&caller_private_key, "credits.aleo", "transfer", [r0, r1, r2].into_iter()).unwrap();

        // LEAVE WASM: Get this data from the web (not in rust)
        let (state_root, commitment_map) = get_inclusion_proof_data(&commitments); // This would be inserted into the main

        // ENTER WASM: Execute the program in wasm with data supplied from an outside environment
        let (_, execution, _, _) = execute_program(
            "credits.aleo",
            "transfer",
            authorization,
            state_root,
            commitment_map,
            credits_proving_key,
            inclusion_proving_key,
        )
        .unwrap();

        // ENTER WASM: Verify the execution
        assert!(Inclusion::verify_execution(&execution, Some(inclusion_verifying_key)).is_ok());
    }
}
