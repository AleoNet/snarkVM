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

macro_rules! prepare_fee_impl {
    ($self:ident, $fee_transition:ident, $query:ident, $get_state_path_for_commitment:ident $(, $await:ident)?) => {{
        // Ensure the fee has the correct program ID.
        let fee_program_id = ProgramID::from_str("credits.aleo")?;
        ensure!(*$fee_transition.program_id() == fee_program_id, "Incorrect program ID for fee");

        // Ensure the fee has the correct function.
        let fee_function = Identifier::from_str("fee")?;
        ensure!(*$fee_transition.function_name() == fee_function, "Incorrect function name for fee");

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
                        !task.is_local,
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
        ensure!(!assignments.is_empty(), "Inclusion expected the assignments for the fee to *not* be empty");

        // Return the assignments.
        Ok(assignments)
    }};
}

impl<N: Network> Inclusion<N> {
    /// Returns the inclusion assignments for the given fee transition.
    pub fn prepare_fee<B: BlockStorage<N>, Q: Into<Query<N, B>>>(
        &self,
        fee_transition: &Transition<N>,
        query: Q,
    ) -> Result<Vec<InclusionAssignment<N>>> {
        let query = query.into();
        prepare_fee_impl!(self, fee_transition, query, get_state_path_for_commitment)
    }

    /// Returns the inclusion assignments for the given fee transition.
    pub async fn prepare_fee_async<B: BlockStorage<N>, Q: Into<Query<N, B>>>(
        &self,
        fee_transition: &Transition<N>,
        query: Q,
    ) -> Result<Vec<InclusionAssignment<N>>> {
        let query = query.into();
        prepare_fee_impl!(self, fee_transition, query, get_state_path_for_commitment_async, await)
    }

    pub fn fee_global_state_root(assignments: &Vec<InclusionAssignment<N>>) -> Result<N::StateRoot> {
        // Initialize the global state root.
        let mut global_state_root = N::StateRoot::default();

        for assignment in assignments {
            // Ensure the global state root is the same across iterations.
            let assignment_global_state_root = assignment.global_state_root();
            if *global_state_root != Field::zero() && global_state_root != assignment_global_state_root {
                bail!("Inclusion expected the global state root to be the same across iterations")
            }
            // Update the global state root.
            global_state_root = assignment_global_state_root;
        }

        // Ensure the global state root is not zero.
        if *global_state_root == Field::zero() {
            bail!("Inclusion expected the global state root in the execution to *not* be zero")
        }

        Ok(global_state_root)
    }

    /// Checks the inclusion proof for the fee.
    /// Note: This does *not* check that the global state root exists in the ledger.
    pub fn prepare_verify_fee(fee: &Fee<N>) -> Result<(VerifyingKey<N>, Vec<Vec<N::Field>>)> {
        // Retrieve the global state root.
        let global_state_root = fee.global_state_root();

        // Ensure the global state root is not zero.
        if *global_state_root == Field::zero() {
            bail!("Inclusion expected the global state root in the fee to *not* be zero")
        }

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
        Ok((verifying_key, batch_verifier_inputs))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_utilities::TestRng;

    #[test]
    fn test_inclusion_verify_fee() {
        let rng = &mut TestRng::default();
        // Fetch a deployment transaction.
        let deployment_transaction = crate::vm::test_helpers::sample_deployment_transaction(rng);

        match deployment_transaction {
            Transaction::Deploy(_, _, _, fee) => {
                let result = Inclusion::prepare_verify_fee(&fee);
                assert!(result.is_ok());
                let (_vk, inputs) = result.unwrap();
                assert_eq!(inputs.len(), 1);
                // We do not test inclusion individually, as we have tests to batch verify it with transitions elsewhere
            }
            _ => panic!("Expected a deployment transaction"),
        }
    }
}
