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

use console::{
    prelude::One,
    types::{Scalar, I128, I16, I32, I64, I8, U128, U16, U32, U8},
};
use synthesizer_program::For;

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

                    // Initialize a stack for the loop headers.
                    let mut loop_stack: Vec<(usize, Literal<N>)> = Vec::new();

                    // Initialize a mask to skip the next command.
                    let mut skip_next_command = false;

                    // Initialize a variable to track the number of skipped for loops.
                    let mut skipped_for_loops = 0;

                    // Evaluate the commands.
                    while counter < finalize.commands().len() {
                        // Retrieve the command.
                        let command = &finalize.commands()[counter];
                        // Finalize the command.
                        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| match &command {
                            Command::BranchEq(branch_eq) if !skip_next_command => {
                                counter = branch_to(counter, branch_eq, finalize, stack, &registers)?;
                                Ok(None)
                            }
                            Command::BranchNeq(branch_neq) if !skip_next_command => {
                                counter = branch_to(counter, branch_neq, finalize, stack, &registers)?;
                                Ok(None)
                            }
                            Command::For(for_) => {
                                if skip_next_command {
                                    skipped_for_loops += 1;
                                } else {
                                    (counter, skip_next_command) =
                                        begin_iteration(counter, for_, stack, &mut registers, &mut loop_stack)?;
                                }
                                Ok(None)
                            }
                            Command::EndFor(_) => {
                                if skip_next_command {
                                    skipped_for_loops -= 1;
                                    counter += 1;
                                    if skipped_for_loops == 0 {
                                        loop_stack.pop();
                                        skip_next_command = false;
                                    }
                                } else {
                                    counter = loop_stack.last().unwrap().0
                                }
                                Ok(None)
                            }
                            _ if !skip_next_command => {
                                let operation = command.finalize(stack, store, &mut registers);
                                counter += 1;
                                operation
                            }
                            _ => {
                                counter += 1;
                                Ok(None)
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
        Some(index) => Ok(*index),
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

// A helper function that begins an iteration of a for loop.
#[inline]
fn begin_iteration<N: Network>(
    counter: usize,
    for_: &For<N>,
    stack: &Stack<N>,
    registers: &mut FinalizeRegisters<N>,
    loop_stack: &mut Vec<(usize, Literal<N>)>,
) -> Result<(usize, bool)> {
    // Set the loop register to the appropriate value.
    match loop_stack.last() {
        // If the counter matches the index of the last entry on the loop stack, then this is at least the second iteration of the loop.
        Some((i, current)) if *i == counter => {
            // Load the end of the range.
            let end = registers.load_literal(stack, for_.range().end())?;
            // Compare the values and (in/de)crement appropriately.
            let value = match (current, end) {
                (Literal::Field(current), Literal::Field(end)) => {
                    Literal::Field(if current <= &end { current.add(Field::one()) } else { current.sub(Field::one()) })
                }
                (Literal::Scalar(current), Literal::Scalar(end)) => Literal::Scalar(if current <= &end {
                    current.add(Scalar::one())
                } else {
                    current.sub(Scalar::one())
                }),
                (Literal::I8(current), Literal::I8(end)) => {
                    Literal::I8(if current <= &end { current.add(I8::one()) } else { current.sub(I8::one()) })
                }
                (Literal::I16(current), Literal::I16(end)) => {
                    Literal::I16(if current <= &end { current.add(I16::one()) } else { current.sub(I16::one()) })
                }
                (Literal::I32(current), Literal::I32(end)) => {
                    Literal::I32(if current <= &end { current.add(I32::one()) } else { current.sub(I32::one()) })
                }
                (Literal::I64(current), Literal::I64(end)) => {
                    Literal::I64(if current <= &end { current.add(I64::one()) } else { current.sub(I64::one()) })
                }
                (Literal::I128(current), Literal::I128(end)) => {
                    Literal::I128(if current <= &end { current.add(I128::one()) } else { current.sub(I128::one()) })
                }
                (Literal::U8(current), Literal::U8(end)) => {
                    Literal::U8(if current <= &end { current.add(U8::one()) } else { current.sub(U8::one()) })
                }
                (Literal::U16(current), Literal::U16(end)) => {
                    Literal::U16(if current <= &end { current.add(U16::one()) } else { current.sub(U16::one()) })
                }
                (Literal::U32(current), Literal::U32(end)) => {
                    Literal::U32(if current <= &end { current.add(U32::one()) } else { current.sub(U32::one()) })
                }
                (Literal::U64(current), Literal::U64(end)) => {
                    Literal::U64(if current <= &end { current.add(U64::one()) } else { current.sub(U64::one()) })
                }
                (Literal::U128(current), Literal::U128(end)) => {
                    Literal::U128(if current <= &end { current.add(U128::one()) } else { current.sub(U128::one()) })
                }
                _ => bail!("Incompatible types for the loop counter and range."),
            };
            // Store the new value.
            registers.store_literal(stack, for_.register(), value.clone())?;
            // Update the loop stack.
            loop_stack.last_mut().unwrap().1 = value;
        }
        // Otherwise, this is the first iteration.
        _ => {
            // Get the value of the start of the range.
            let start_value = registers.load_literal(stack, for_.range().start())?;
            registers.store_literal(stack, for_.register(), start_value.clone())?;
            // Push the current index and value to the loop stack.
            loop_stack.push((counter, start_value));
        }
    }

    // Get the current value of the loop counter.
    let current = &loop_stack.last().unwrap().1;
    // If the the value is equal to the end of the range, then the loop is complete.
    let is_complete = current == &registers.load_literal(stack, for_.range().end())?;

    Ok((counter + 1, is_complete))
}

// A helper function that ends an iteration of a for loop.

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
