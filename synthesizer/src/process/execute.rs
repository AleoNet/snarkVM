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

use crate::{Key, KeyBatch, KeyMode, ProvingKeyId};

impl<N: Network> Process<N> {
    /// Executes the given authorization.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        execution: &mut Execution<N>,
        transition_assignments: BTreeMap<ProvingKeyId<N>, Vec<&Assignment<N::Field>>>,
        inclusion_assignments: Option<Vec<&Assignment<N::Field>>>,
        rng: &mut R,
    ) -> Result<()> {
        let timer = timer!("Process::execute");

        // Retrieve the proving keys and fill the batch.
        let mut batch = KeyBatch::new(1 + transition_assignments.len(), KeyMode::Proving);
        let mut assignments = Vec::with_capacity(1 + transition_assignments.len());
        let mut function_names = Vec::with_capacity(1 + transition_assignments.len());
        for (proving_key_id, transition_assignments) in transition_assignments.iter() {
            let proving_key = self.get_proving_key(proving_key_id.program_id, proving_key_id.function_name)?;
            // NOTE: consistent ordering of keys and assignments is crucial
            batch.add(Key::ProvingKey(proving_key))?;
            assignments.push(transition_assignments);
            function_names.push(&proving_key_id.function_name);
        }

        let inclusion_name = Identifier::<N>::from_str(N::INCLUSION_FUNCTION_NAME)?;
        if let Some(inclusion_assignments) = inclusion_assignments.as_ref() {
            let inclusion_key = ProvingKey::<N>::new(N::inclusion_proving_key().clone());
            batch.add(Key::ProvingKey(inclusion_key))?;
            assignments.push(inclusion_assignments);
            function_names.push(&inclusion_name);
        }

        execution.prove(batch, assignments.as_slice(), function_names.as_slice(), rng)?;

        finish!(timer);
        Ok(())
    }

    /// Verifies the given execution is valid.
    /// Note: This does *not* check that the global state root exists in the ledger.
    #[inline]
    pub fn verify_execution(&self, execution: &Execution<N>) -> Result<()> {
        let timer = timer!("Process::verify_execution");

        // Ensure the execution contains transitions.
        ensure!(!execution.is_empty(), "There are no transitions in the execution");

        // Ensure the number of transitions matches the program function.
        {
            // Retrieve the transition (without popping it).
            let transition = execution.peek()?;
            // Retrieve the stack.
            let stack = self.get_stack(transition.program_id())?;
            // Ensure the number of calls matches the number of transitions.
            let number_of_calls = stack.get_number_of_calls(transition.function_name())?;
            ensure!(
                number_of_calls == execution.len(),
                "The number of transitions in the execution is incorrect. Expected {number_of_calls}, but found {}",
                execution.len()
            );
        }
        lap!(timer, "Verify the number of transitions");

        // Replicate the execution stack for verification.
        let mut queue = execution.clone();
        let mut transition_assignments = BTreeMap::<_, Vec<_>>::new();
        let mut batch = KeyBatch::<N>::new(1 + execution.transitions().len(), KeyMode::Verifying);
        let mut all_inputs = Vec::with_capacity(1 + execution.transitions().len());

        // Verify each transition.
        while let Ok(transition) = queue.pop() {
            #[cfg(debug_assertions)]
            println!("Verifying transition for {}/{}...", transition.program_id(), transition.function_name());

            // Ensure the transition ID is correct.
            ensure!(**transition.id() == transition.to_root()?, "The transition ID is incorrect");
            // Ensure the number of inputs is within the allowed range.
            ensure!(transition.inputs().len() <= N::MAX_INPUTS, "Transition exceeded maximum number of inputs");
            // Ensure the number of outputs is within the allowed range.
            ensure!(transition.outputs().len() <= N::MAX_INPUTS, "Transition exceeded maximum number of outputs");

            // Compute the function ID as `Hash(network_id, program_id, function_name)`.
            let function_id = N::hash_bhp1024(
                &(
                    U16::<N>::new(N::ID),
                    transition.program_id().name(),
                    transition.program_id().network(),
                    transition.function_name(),
                )
                    .to_bits_le(),
            )?;

            // Ensure each input is valid.
            if transition
                .inputs()
                .iter()
                .enumerate()
                .any(|(index, input)| !input.verify(function_id, transition.tcm(), index))
            {
                bail!("Failed to verify a transition input")
            }
            lap!(timer, "Verify the inputs");

            // Ensure each output is valid.
            let num_inputs = transition.inputs().len();
            if transition
                .outputs()
                .iter()
                .enumerate()
                .any(|(index, output)| !output.verify(function_id, transition.tcm(), num_inputs + index))
            {
                bail!("Failed to verify a transition output")
            }
            lap!(timer, "Verify the outputs");

            // Compute the x- and y-coordinate of `tpk`.
            let (tpk_x, tpk_y) = transition.tpk().to_xy_coordinates();

            // [Inputs] Construct the verifier inputs to verify the proof.
            let mut inputs = vec![N::Field::one(), *tpk_x, *tpk_y, **transition.tcm()];
            // [Inputs] Extend the verifier inputs with the input IDs.
            inputs.extend(transition.inputs().iter().flat_map(|input| input.verifier_inputs()));

            // Retrieve the stack.
            let stack = self.get_stack(transition.program_id())?;
            // Retrieve the function from the stack.
            let function = stack.get_function(transition.function_name())?;
            // Determine the number of function calls in this function.
            let mut num_function_calls = 0;
            for instruction in function.instructions() {
                if let Instruction::Call(call) = instruction {
                    // Determine if this is a function call.
                    if call.is_function_call(stack)? {
                        num_function_calls += 1;
                    }
                }
            }
            // If there are function calls, append their inputs and outputs.
            if num_function_calls > 0 {
                // This loop takes the last `num_function_call` transitions, and reverses them
                // to order them in the order they were defined in the function.
                for transition in queue.transitions().rev().take(num_function_calls).rev() {
                    // [Inputs] Extend the verifier inputs with the input IDs of the external call.
                    inputs.extend(transition.inputs().iter().flat_map(|input| input.verifier_inputs()));
                    // [Inputs] Extend the verifier inputs with the output IDs of the external call.
                    inputs.extend(transition.output_ids().map(|id| **id));
                }
            }

            // [Inputs] Extend the verifier inputs with the output IDs.
            inputs.extend(transition.outputs().iter().flat_map(|output| output.verifier_inputs()));

            // Ensure the transition contains finalize inputs, if the function has a finalize scope.
            if let Some((command, logic)) = function.finalize() {
                // Ensure the transition contains finalize inputs.
                match transition.finalize() {
                    Some(finalize) => {
                        // Retrieve the number of operands.
                        let num_operands = command.operands().len();
                        // Retrieve the number of inputs.
                        let num_inputs = logic.inputs().len();

                        // Ensure the number of inputs for finalize is within the allowed range.
                        ensure!(finalize.len() <= N::MAX_INPUTS, "Transition exceeds maximum inputs for finalize");
                        // Ensure the number of inputs for finalize matches in the finalize command.
                        ensure!(finalize.len() == num_operands, "The number of inputs for finalize is incorrect");
                        // Ensure the number of inputs for finalize matches in the finalize logic.
                        ensure!(finalize.len() == num_inputs, "The number of inputs for finalize is incorrect");

                        // Convert the finalize inputs into concatenated bits.
                        let finalize_bits = finalize.iter().flat_map(ToBits::to_bits_le).collect::<Vec<_>>();
                        // Compute the checksum of the finalize inputs.
                        let checksum = N::hash_bhp1024(&finalize_bits)?;

                        // [Inputs] Extend the verifier inputs with the inputs for finalize.
                        inputs.push(*checksum);
                    }
                    None => bail!("The transition is missing inputs for 'finalize'"),
                }
            }

            let pk_id =
                ProvingKeyId { program_id: *transition.program_id(), function_name: *transition.function_name() };
            if let Some(assignment) = transition_assignments.get_mut(&pk_id) {
                assignment.push(inputs);
            } else {
                transition_assignments.insert(pk_id, vec![inputs]);
            }

            lap!(timer, "Construct the verifier inputs");

            #[cfg(debug_assertions)]
            println!("Transition public inputs ({} elements): {:#?}", all_inputs.len(), all_inputs);

            lap!(timer, "Verify transition for {}", function.name());
        }

        for (pkid, circuit_inputs) in transition_assignments {
            // Retrieve the verifying key.
            let verifying_key = self.get_verifying_key(pkid.program_id, pkid.function_name)?;
            batch.add(Key::VerifyingKey(verifying_key))?;
            all_inputs.push(circuit_inputs);
        }

        // Ensure the inclusion proof is valid.
        if execution.proves_inclusion() {
            let (inclusion_vk, inclusion_inputs) = Inclusion::prepare_verify_execution(execution)?;
            batch.add(Key::VerifyingKey(inclusion_vk))?;
            all_inputs.push(inclusion_inputs);
        }

        // Ensure the transition proofs are all valid.
        ensure!(execution.verify(batch, all_inputs.as_slice())?, "Execution is invalid - failed to verify proof");
        lap!(timer, "Verify execution proof");

        finish!(timer);
        Ok(())
    }
}
