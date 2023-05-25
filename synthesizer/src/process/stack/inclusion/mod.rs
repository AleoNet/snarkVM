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

mod execute;
mod fee;

#[cfg(debug_assertions)]
use crate::Stack;
use crate::{BlockStorage, Execution, Fee, Input, Output, Query, Transaction, Transition};
use console::{
    network::prelude::*,
    program::{Identifier, InputID, ProgramID, StatePath, TransactionLeaf, TransitionLeaf, TRANSACTION_DEPTH},
    types::{Field, Group},
};
use snarkvm_synthesizer_snark::{Proof, ProvingKey, VerifyingKey};

use std::collections::HashMap;

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
        assert_eq!(A::count(), (0, 1, 0, 0, (0, 0, 0)));
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
