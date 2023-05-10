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
    /// Finalizes the deployment.
    /// This method assumes the given deployment **is valid**.
    /// This method should **only** be called by `VM::finalize()`.
    #[inline]
    pub(crate) fn finalize_deployment<P: FinalizeStorage<N>>(
        &self,
        store: &FinalizeStore<N, P>,
        deployment: &Deployment<N>,
    ) -> Result<(Stack<N>, Vec<FinalizeOperation<N>>)> {
        let timer = timer!("Process::finalize_deployment");

        // Compute the program stack.
        let stack = Stack::new(self, deployment.program())?;
        lap!(timer, "Compute the stack");

        // Insert the verifying keys.
        for (function_name, (verifying_key, _)) in deployment.verifying_keys() {
            stack.insert_verifying_key(function_name, verifying_key.clone())?;
        }
        lap!(timer, "Insert the verifying keys");

        // Retrieve the program ID.
        let program_id = deployment.program_id();

        // Initialize the mappings, and store their finalize operations.
        atomic_batch_scope!(store, {
            // Initialize a list for the finalize operations.
            let mut finalize_operations = Vec::with_capacity(deployment.program().mappings().len());

            // Iterate over the mappings.
            for mapping in deployment.program().mappings().values() {
                // Initialize the mapping.
                finalize_operations.push(store.initialize_mapping(program_id, mapping.name())?);
            }
            lap!(timer, "Initialize the program mappings");

            finish!(timer);

            // Return the stack and finalize operations.
            Ok((stack, finalize_operations))
        })
    }

    /// Finalizes the execution.
    /// This method assumes the given execution **is valid**.
    /// This method should **only** be called by `VM::finalize()`.
    #[inline]
    pub(crate) fn finalize_execution<P: FinalizeStorage<N>>(
        &self,
        store: &FinalizeStore<N, P>,
        execution: &Execution<N>,
    ) -> Result<Vec<FinalizeOperation<N>>> {
        let timer = timer!("Program::finalize_execution");

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

        atomic_batch_scope!(store, {
            // Initialize a list for finalize operations.
            let mut finalize_operations = Vec::new();

            // TODO (howardwu): This is a temporary approach. We should create a "CallStack" and recurse through the stack.
            //  Currently this loop assumes a linearly execution stack.
            // Finalize each transition, starting from the last one.
            for transition in execution.transitions() {
                #[cfg(debug_assertions)]
                println!("Finalizing transition for {}/{}...", transition.program_id(), transition.function_name());

                // Retrieve the stack.
                let stack = self.get_stack(transition.program_id())?;
                // Retrieve the function name.
                let function_name = transition.function_name();

                // If there is a finalize scope, finalize the function.
                if let Some((_, finalize)) = stack.get_function(function_name)?.finalize() {
                    // Retrieve the finalize inputs.
                    let inputs = match transition.finalize() {
                        Some(inputs) => inputs,
                        // Ensure the transition contains finalize inputs.
                        None => bail!("The transition is missing inputs for 'finalize'"),
                    };

                    // Initialize the registers.
                    let mut registers = FinalizeRegisters::<N>::new(stack.get_finalize_types(finalize.name())?.clone());

                    // Store the inputs.
                    finalize.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(
                        |(register, input)| {
                            // Assign the input value to the register.
                            registers.store(stack, register, input.clone())
                        },
                    )?;

                    // Evaluate the commands.
                    for command in finalize.commands() {
                        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            command.finalize(stack, store, &mut registers)
                        }));
                        match result {
                            // If the evaluation succeeds with an operation, add it to the list.
                            Ok(Ok(Some(finalize_operation))) => finalize_operations.push(finalize_operation),
                            // If the evaluation succeeds with no operation, continue.
                            Ok(Ok(None)) => (),
                            // If the evaluation fails, bail and return the error.
                            Ok(Err(error)) => bail!("'finalize' failed to evaluate command ({command}): {error}"),
                            // If the evaluation fails, bail and return the error.
                            Err(_) => bail!("'finalize' failed to evaluate command ({command})"),
                        }
                    }

                    lap!(timer, "Finalize transition for {function_name}");
                }
            }
            finish!(timer);

            // Return the finalize operations.
            Ok(finalize_operations)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_utilities::TestRng;

    type CurrentAleo = circuit::network::AleoV0;

    #[test]
    fn test_finalize_deployment() {
        let rng = &mut TestRng::default();

        // Fetch the program from the deployment.
        let program = crate::vm::test_helpers::sample_program();
        // Initialize a new process.
        let mut process = Process::load().unwrap();
        // Deploy the program.
        let deployment = process.deploy::<CurrentAleo, _>(&program, rng).unwrap();

        // Initialize a new VM.
        let vm = crate::vm::test_helpers::sample_vm();

        // Ensure the program does not exist.
        assert!(!process.contains_program(program.id()));

        // Finalize the deployment.
        let (stack, _) = process.finalize_deployment(vm.finalize_store(), &deployment).unwrap();
        // Add the stack *manually* to the process.
        process.add_stack(stack);

        // Ensure the program exists.
        assert!(process.contains_program(program.id()));
    }
}
