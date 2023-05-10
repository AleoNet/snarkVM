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

impl<N: Network> Process<N> {
    /// Executes the given authorization.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        authorization: Authorization<N>,
        rng: &mut R,
    ) -> Result<(Response<N>, Execution<N>, Inclusion<N>, Vec<CallMetrics<N>>)> {
        let timer = timer!("Process::execute");

        // Retrieve the main request (without popping it).
        let request = authorization.peek_next()?;

        #[cfg(feature = "aleo-cli")]
        println!("{}", format!(" • Executing '{}/{}'...", request.program_id(), request.function_name()).dimmed());

        // Initialize the execution.
        let execution = Arc::new(RwLock::new(Execution::new()));
        // Initialize the inclusion.
        let inclusion = Arc::new(RwLock::new(Inclusion::new()));
        // Initialize the metrics.
        let metrics = Arc::new(RwLock::new(Vec::new()));
        // Initialize the call stack.
        let call_stack = CallStack::execute(authorization, execution.clone(), inclusion.clone(), metrics.clone())?;
        lap!(timer, "Initialize call stack");
        // Execute the circuit.
        let response = self.get_stack(request.program_id())?.execute_function::<A, R>(call_stack, rng)?;
        lap!(timer, "Execute the function");
        // Extract the execution.
        let execution = Arc::try_unwrap(execution).unwrap().into_inner();
        // Ensure the execution is not empty.
        ensure!(!execution.is_empty(), "Execution of '{}/{}' is empty", request.program_id(), request.function_name());
        // Extract the inclusion.
        let inclusion = Arc::try_unwrap(inclusion).unwrap().into_inner();
        // Extract the metrics.
        let metrics = Arc::try_unwrap(metrics).unwrap().into_inner();

        finish!(timer);
        Ok((response, execution, inclusion, metrics))
    }

    /// Verifies the given execution is valid.
    /// Note: This does *not* check that the global state root exists in the ledger.
    #[inline]
    pub fn verify_execution<const VERIFY_INCLUSION: bool>(&self, execution: &Execution<N>) -> Result<()> {
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

        // Ensure the inclusion proof is valid.
        if VERIFY_INCLUSION {
            Inclusion::verify_execution(execution)?;
            lap!(timer, "Verify the inclusion proof");
        }

        // Replicate the execution stack for verification.
        let mut queue = execution.clone();

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

            lap!(timer, "Construct the verifier inputs");

            #[cfg(debug_assertions)]
            println!("Transition public inputs ({} elements): {:#?}", inputs.len(), inputs);

            // Retrieve the verifying key.
            let verifying_key = self.get_verifying_key(stack.program_id(), function.name())?;
            // Ensure the transition proof is valid.
            ensure!(
                verifying_key.verify(function.name(), &inputs, transition.proof()),
                "Transition is invalid - failed to verify transition proof"
            );

            lap!(timer, "Verify transition proof for {}", function.name());
        }

        finish!(timer);
        Ok(())
    }
}
