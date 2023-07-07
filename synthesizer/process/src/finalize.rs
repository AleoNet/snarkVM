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
    /// Finalizes the deployment.
    /// This method assumes the given deployment **is valid**.
    /// This method should **only** be called by `VM::finalize()`.
    #[inline]
    pub fn finalize_deployment<P: FinalizeStorage<N>>(
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
    pub fn finalize_execution<P: FinalizeStorage<N>>(
        &self,
        state: FinalizeGlobalState,
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
                    let mut registers = FinalizeRegisters::<N>::new(
                        state,
                        *transition.id(),
                        *function_name,
                        stack.get_finalize_types(finalize.name())?.clone(),
                    );

                    // Store the inputs.
                    finalize.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(
                        |(register, input)| {
                            // Assign the input value to the register.
                            registers.store(stack, register, input.clone())
                        },
                    )?;

                    // Initialize a counter for the index of the commands.
                    let mut counter = 0;

                    // Evaluate the commands.
                    while counter < finalize.commands().len() {
                        // Retrieve the command.
                        let command = &finalize.commands()[counter];
                        // Finalize the command.
                        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| match &command {
                            Command::BranchEq(branch_eq) => {
                                counter = branch_to(counter, branch_eq, finalize, stack, &registers)?;
                                Ok(None)
                            }
                            Command::BranchNeq(branch_neq) => {
                                counter = branch_to(counter, branch_neq, finalize, stack, &registers)?;
                                Ok(None)
                            }
                            _ => {
                                let operations = command.finalize(stack, store, &mut registers);
                                counter += 1;
                                operations
                            }
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

// A helper function that returns the index to branch to.
#[inline]
fn branch_to<N: Network, const VARIANT: u8>(
    counter: usize,
    branch: &Branch<N, VARIANT>,
    finalize: &Finalize<N>,
    stack: &Stack<N>,
    registers: &FinalizeRegisters<N>,
) -> Result<usize> {
    // Retrieve the inputs.
    let first = registers.load(stack, branch.first())?;
    let second = registers.load(stack, branch.second())?;

    // A helper to get the index corresponding to a position.
    let get_position_index = |position: &Identifier<N>| match finalize.positions().get(position) {
        Some(index) if *index > counter => Ok(*index),
        Some(_) => bail!("Cannot branch to an earlier position '{position}' in the program"),
        None => bail!("The position '{position}' does not exist."),
    };

    // Compare the operands and determine the index to branch to.
    match VARIANT {
        // The `branch.eq` variant.
        0 if first == second => get_position_index(branch.position()),
        0 if first != second => Ok(counter + 1),
        // The `branch.neq` variant.
        1 if first == second => Ok(counter + 1),
        1 if first != second => get_position_index(branch.position()),
        _ => bail!("Invalid 'branch' variant: {VARIANT}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::prelude::TestRng;
    use ledger_store::helpers::memory::FinalizeMemory;

    type CurrentNetwork = console::network::Testnet3;
    type CurrentAleo = circuit::network::AleoV0;

    #[test]
    fn test_finalize_deployment() {
        let rng = &mut TestRng::default();

        // Initialize a new program.
        let program = Program::<CurrentNetwork>::from_str(
            r"
program testing.aleo;

struct message:
    amount as u128;

mapping account:
    key owner as address.public;
    value amount as u64.public;

record token:
    owner as address.private;
    amount as u64.private;

function mint:
    input r0 as address.private;
    input r1 as u64.private;
    cast r0 r1 into r2 as token.record;
    output r2 as token.record;

function compute:
    input r0 as message.private;
    input r1 as message.public;
    input r2 as message.private;
    input r3 as token.record;
    add r0.amount r1.amount into r4;
    cast r3.owner r3.amount into r5 as token.record;
    output r4 as u128.public;
    output r5 as token.record;",
        )
        .unwrap();

        // Initialize a new process.
        let mut process = Process::load().unwrap();
        // Deploy the program.
        let deployment = process.deploy::<CurrentAleo, _>(&program, rng).unwrap();

        // Initialize a new finalize store.
        let finalize_store = FinalizeStore::<_, FinalizeMemory<_>>::open(None).unwrap();

        // Ensure the program does not exist.
        assert!(!process.contains_program(program.id()));

        // Finalize the deployment.
        let (stack, _) = process.finalize_deployment(&finalize_store, &deployment).unwrap();
        // Add the stack *manually* to the process.
        process.add_stack(stack);

        // Ensure the program exists.
        assert!(process.contains_program(program.id()));
    }
}
