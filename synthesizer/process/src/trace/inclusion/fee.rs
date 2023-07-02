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

macro_rules! prepare_fee_impl {
    ($self:ident, $fee_transition:ident, $query:ident, $get_state_path_for_commitment:ident $(, $await:ident)?) => {{
        // Ensure the fee has the correct program ID and function.
        ensure!($fee_transition.is_fee(), "Incorrect transition type for the fee, expected 'credits.aleo/fee'");

        // Initialize an empty transaction tree.
        let transaction_tree = N::merkle_tree_bhp::<TRANSACTION_DEPTH>(&[])?;
        // Initialize the global state root.
        let mut global_state_root = N::StateRoot::default();
        // Initialize a vector for the assignments.
        let mut assignments = vec![];

        // Process the input tasks.
        match $self.input_tasks.get($fee_transition.id()) {
            Some(tasks) => {
                for task in tasks {
                    // Retrieve the local state root.
                    let local_state_root = (*transaction_tree.root()).into();
                    // Construct the state path.
                    let state_path = {
                        $query.$get_state_path_for_commitment(&task.commitment)
                        $(.$await)?
                    }?;

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
                        task.local.is_none(), // Equivalent to 'is_global'.
                    );

                    // Add the assignment to the assignments.
                    assignments.push(assignment);
                }
            }
            None => bail!("Missing input state for fee transition {} in inclusion", $fee_transition.id()),
        }

        // Ensure the global state root is not zero.
        if *global_state_root == Field::zero() {
            bail!("Inclusion expected the global state root in the fee to *not* be zero")
        }
        // Ensure the assignments are not empty.
        if assignments.is_empty() {
            bail!("Inclusion expected the assignments for the fee to *not* be empty")
        }
        // Return the assignments and global state root.
        Ok((assignments, global_state_root))
    }};
}

impl<N: Network> Inclusion<N> {
    /// Returns the inclusion assignments for the given fee transition.
    pub fn prepare_fee(
        &self,
        fee_transition: &Transition<N>,
        query: impl QueryTrait<N>,
    ) -> Result<(Vec<InclusionAssignment<N>>, N::StateRoot)> {
        prepare_fee_impl!(self, fee_transition, query, get_state_path_for_commitment)
    }

    /// Returns the inclusion assignments for the given fee transition.
    #[cfg(feature = "async")]
    pub async fn prepare_fee_async(
        &self,
        fee_transition: &Transition<N>,
        query: impl QueryTrait<N>,
    ) -> Result<(Vec<InclusionAssignment<N>>, N::StateRoot)> {
        prepare_fee_impl!(self, fee_transition, query, get_state_path_for_commitment_async, await)
    }
}
