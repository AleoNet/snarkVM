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

#[derive(Copy, Clone, Debug)]
pub enum FinalizeMode {
    /// Invoke finalize as a real run.
    RealRun,
    /// Invoke finalize as a dry run.
    DryRun,
}

impl FinalizeMode {
    /// Returns the u8 value of the finalize mode.
    #[inline]
    pub const fn to_u8(self) -> u8 {
        match self {
            Self::RealRun => 0,
            Self::DryRun => 1,
        }
    }

    /// Returns a finalize mode from a given u8.
    #[inline]
    pub fn from_u8(value: u8) -> Result<Self> {
        match value {
            0 => Ok(Self::RealRun),
            1 => Ok(Self::DryRun),
            _ => bail!("Invalid finalize mode of '{value}'"),
        }
    }
}

impl<N: Network> Process<N> {
    /// Finalizes the deployment.
    /// This method assumes the given deployment **is valid**.
    #[inline]
    pub fn finalize_deployment<P: FinalizeStorage<N>, const FINALIZE_MODE: u8>(
        &mut self,
        store: &FinalizeStore<N, P>,
        deployment: &Deployment<N>,
    ) -> Result<Vec<FinalizeOperation<N>>> {
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

        // Initialize a list for the finalize operations.
        let finalize_operations = Arc::new(Mutex::new(Vec::with_capacity(deployment.program().mappings().len())));

        // Initialize the mappings, and store their finalize operations.
        atomic_write_batch!(store, {
            // Iterate over the mappings.
            for mapping in deployment.program().mappings().values() {
                // Initialize the mapping.
                finalize_operations.lock().push(store.initialize_mapping(program_id, mapping.name())?);
            }

            // Handle the atomic batch, based on the finalize mode.
            match FinalizeMode::from_u8(FINALIZE_MODE)? {
                // If this is a real run, commit the atomic batch.
                FinalizeMode::RealRun => Ok(()),
                // If this is a dry run, abort the atomic batch.
                FinalizeMode::DryRun => bail!("Dry run of finalize deployment for '{program_id}'"),
            }
        });
        lap!(timer, "Initialize the program mappings");

        // If this is a real run, update the stack.
        if FINALIZE_MODE == FinalizeMode::RealRun.to_u8() {
            // Add the stack to the process.
            self.stacks.insert(*deployment.program_id(), stack);
        }

        finish!(timer);

        // Return the finalize operations.
        Ok(Arc::try_unwrap(finalize_operations).unwrap().into_inner())
    }

    /// Finalizes the execution.
    /// This method assumes the given execution **is valid**.
    #[inline]
    pub fn finalize_execution<P: FinalizeStorage<N>, const FINALIZE_MODE: u8>(
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

        // Initialize a list for finalize operations.
        let finalize_operations = Arc::new(Mutex::new(Vec::new()));

        atomic_write_batch!(store, {
            // TODO (howardwu): This is a temporary approach. We should create a "CallStack" and recurse through the stack.
            //  Currently this loop assumes a linearly execution stack.
            // Finalize each transition, starting from the last one.
            for transition in execution.transitions().rev() {
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
                        match command.finalize(stack, store, &mut registers) {
                            // If the evaluation succeeds with an operation, add it to the list.
                            Ok(Some(finalize_operation)) => finalize_operations.lock().push(finalize_operation),
                            // If the evaluation succeeds with no operation, continue.
                            Ok(None) => (),
                            // If the evaluation fails, bail and return the error.
                            Err(error) => bail!("'finalize' failed to evaluate command ({command}): {error}"),
                        }
                    }

                    lap!(timer, "Finalize transition for {function_name}");
                }
            }

            // Handle the atomic batch, based on the finalize mode.
            match FinalizeMode::from_u8(FINALIZE_MODE)? {
                // If this is a real run, commit the atomic batch.
                FinalizeMode::RealRun => Ok(()),
                // If this is a dry run, abort the atomic batch.
                FinalizeMode::DryRun => bail!("Dry run of finalize execution"),
            }
        });
        finish!(timer);

        // Return the finalize operations.
        Ok(Arc::try_unwrap(finalize_operations).unwrap().into_inner())
    }
}
