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

impl<N: Network> Process<N> {
    /// Executes the given authorization.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N>>(
        &self,
        authorization: Authorization<N>,
    ) -> Result<(Response<N>, Trace<N>)> {
        let timer = timer!("Process::execute");

        // Retrieve the main request (without popping it).
        let request = authorization.peek_next()?;
        // Construct the locator.
        let locator = Locator::new(*request.program_id(), *request.function_name());

        #[cfg(feature = "aleo-cli")]
        println!("{}", format!(" • Executing '{locator}'...",).dimmed());

        // Initialize the trace.
        let trace = Arc::new(RwLock::new(Trace::new()));
        // Initialize the call stack.
        let call_stack = CallStack::execute(authorization, trace.clone())?;
        lap!(timer, "Initialize call stack");

        // Execute the circuit.
        let response = self.get_stack(request.program_id())?.execute_function::<A>(call_stack)?;
        lap!(timer, "Execute the function");

        // Extract the trace.
        let trace = Arc::try_unwrap(trace).unwrap().into_inner();
        // Ensure the trace is not empty.
        ensure!(!trace.transitions().is_empty(), "Execution of '{locator}' is empty");

        finish!(timer);
        Ok((response, trace))
    }

    /// Verifies the given execution is valid.
    /// Note: This does *not* check that the global state root exists in the ledger.
    #[inline]
    pub fn verify_execution(&self, execution: &Execution<N>) -> Result<()> {
        let timer = timer!("Process::verify_execution");

        // Ensure the execution contains transitions.
        ensure!(!execution.is_empty(), "There are no transitions in the execution");

        // Ensure the number of transitions matches the program function.
        let locator = {
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
            // Output the locator of the main function.
            Locator::new(*transition.program_id(), *transition.function_name()).to_string()
        };
        lap!(timer, "Verify the number of transitions");

        // Initialize a call graph, which is a map of transition IDs to the transition IDs it calls.
        let mut call_graph = HashMap::new();
        // Initialize a cache for the inputs and outputs of each transition.
        let mut io_cache = HashMap::new();
        // Initialize a mapping from UIDs to transition IDs.
        let mut uid_to_tid = HashMap::new();

        // Metadata for each transition the execution.
        struct TransitionMetadata<N: Network> {
            uid: usize,
            pid: ProgramID<N>,
            fname: Identifier<N>,
            tid: Option<N::TransitionID>,
            children: Vec<usize>,
        }

        impl<N: Network> TransitionMetadata<N> {
            fn new(counter: &mut usize, pid: ProgramID<N>, fname: Identifier<N>, tid: Option<N::TransitionID>) -> Self {
                let uid = *counter;
                *counter += 1;
                Self { uid, pid, fname, tid, children: vec![] }
            }

            fn is_complete(&self) -> bool {
                self.tid.is_some()
            }
        }

        // A helper function to update the call graph.
        let update_call_graph = |metadata: TransitionMetadata<N>,
                                 call_graph: &mut HashMap<N::TransitionID, Vec<N::TransitionID>>,
                                 uid_to_tid: &mut HashMap<usize, N::TransitionID>| {
            // Add an entry to the UID to TID mapping.
            uid_to_tid.insert(metadata.uid, metadata.tid.unwrap());
            // Add an entry to the call graph.
            call_graph.insert(
                metadata.tid.unwrap(),
                metadata.children.into_iter().map(|uid| uid_to_tid[&uid]).collect::<Vec<_>>(),
            );
        };

        // Initialize a stack to track metadata of each transition, while traversing the call graph.
        let mut traversal_stack: Vec<TransitionMetadata<N>> = Vec::new();
        // Initialize a counter to track the unique ID of each transition.
        let mut counter = 0;

        // Iterate over each transition in reverse post-order, and populate the call graph and IO cache.
        for transition in execution.transitions().rev() {
            // Add the transition inputs and outputs to the IO cache.
            io_cache.insert(
                *transition.id(),
                (transition.inputs().to_vec(), transition.output_ids().cloned().collect::<Vec<_>>()),
            );

            // If the stack has entries and they are complete, then pop them.
            while let Some(entry) = traversal_stack.last() {
                if entry.is_complete() {
                    update_call_graph(traversal_stack.pop().unwrap(), &mut call_graph, &mut uid_to_tid);
                } else {
                    break;
                }
            }

            // Now process the current transition.
            match traversal_stack.last_mut() {
                // If the stack is empty, then push the current transition.
                None => {
                    traversal_stack.push(TransitionMetadata::new(
                        &mut counter,
                        *transition.program_id(),
                        *transition.function_name(),
                        Some(*transition.id()),
                    ));
                }
                // If the stack is not empty, then add the current transition ID to the entry.
                Some(head) => {
                    head.tid = Some(*transition.id());
                }
            }
            // Process the entry at the top of the stack.
            // If the entry is complete, then pop it.
            // Note this unwrap is safe, since we just pushed the entry.
            let top = traversal_stack.last().unwrap();
            if !top.children.is_empty() {
                update_call_graph(traversal_stack.pop().unwrap(), &mut call_graph, &mut uid_to_tid);
            } else {
                // Retrieve the stack.
                let stack = self.get_stack(top.pid)?;
                // Retrieve the function from the stack.
                let function = stack.get_function(&top.fname)?;
                // Collect the children of the current transition.
                let children = function
                    .instructions()
                    .iter()
                    .filter_map(|instruction| match instruction {
                        Instruction::Call(call) => Some(call.operator()),
                        _ => None,
                    })
                    .collect::<Vec<_>>();

                // If the function has no children, then pop the entry.
                if children.is_empty() {
                    update_call_graph(traversal_stack.pop().unwrap(), &mut call_graph, &mut uid_to_tid);
                } else {
                    let children = children
                        .into_iter()
                        .map(|call_operator| {
                            let (pid, fname) = match call_operator {
                                crate::CallOperator::Locator(locator) => (locator.program_id(), locator.resource()),
                                crate::CallOperator::Resource(fname) => (&top.pid, fname),
                            };
                            TransitionMetadata::new(&mut counter, *pid, *fname, None)
                        })
                        .collect::<Vec<_>>();

                    // Add the children to the entry.
                    let top = traversal_stack.last_mut().unwrap();
                    top.children.extend(children.iter().map(|child| child.uid));
                    // Push the children to the stack.
                    traversal_stack.extend(children);
                }
            }
        }

        // Empty the stack, checking that all entries are complete.
        while let Some(entry) = traversal_stack.pop() {
            ensure!(entry.is_complete(), "The call graph is incomplete");
            update_call_graph(entry, &mut call_graph, &mut uid_to_tid);
        }

        // Initialize a map of verifying keys to public inputs.
        let mut verifier_inputs = HashMap::new();

        // Verify each transition.
        for transition in execution.transitions() {
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

            // If there are function calls, append their inputs and outputs.
            for transition_id in call_graph.get(transition.id()).unwrap() {
                let (transition_inputs, output_ids) = io_cache.get(transition_id).unwrap();
                // [Inputs] Extend the verifier inputs with the input IDs of the external call.
                inputs.extend(transition_inputs.iter().flat_map(|input| input.verifier_inputs()));
                // [Inputs] Extend the verifier inputs with the output IDs of the external call.
                inputs.extend(output_ids.iter().map(|id| **id));
            }

            // [Inputs] Extend the verifier inputs with the output IDs.
            inputs.extend(transition.outputs().iter().flat_map(|output| output.verifier_inputs()));

            // Retrieve the stack.
            let stack = self.get_stack(transition.program_id())?;
            // Retrieve the function from the stack.
            let function = stack.get_function(transition.function_name())?;

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
            // Save the verifying key and its inputs.
            verifier_inputs
                .entry(Locator::new(*stack.program_id(), *function.name()))
                .or_insert((verifying_key, vec![]))
                .1
                .push(inputs);

            lap!(timer, "Constructed the verifier inputs for a transition of {}", function.name());
        }

        // Count the number of verifier instances.
        let num_instances = verifier_inputs.values().map(|(_, inputs)| inputs.len()).sum::<usize>();
        // Ensure the number of instances matches the number of transitions.
        ensure!(num_instances == execution.transitions().len(), "The number of verifier instances is incorrect");

        // Construct the list of verifier inputs.
        let verifier_inputs = verifier_inputs.values().cloned().collect();
        // Verify the execution proof.
        Trace::verify_execution_proof(&locator, verifier_inputs, execution)?;
        lap!(timer, "Verify the proof");

        finish!(timer);
        Ok(())
    }
}
