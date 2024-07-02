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

impl<N: Network> EpochProgram<N> {
    /// Synthesizes the R1CS for a program function on the given inputs.
    pub fn to_r1cs<A: circuit::Aleo<Network = N>>(&self, console_inputs: Vec<Value<N>>) -> Result<R1CS<A::BaseField>> {
        let timer = timer!("synthesize_r1cs");

        // Declare the function name.
        let function_name = Identifier::from_str("synthesize")?;
        // Retrieve the function from the program.
        let function = self.stack.get_function(&function_name)?;
        // Retrieve the number of function inputs.
        let num_inputs = function.inputs().len();
        // Retrieve the register types for the function.
        let register_types = self.stack.get_register_types(&function_name)?.clone();

        // Ensure the inputs match their expected types.
        ensure!(num_inputs == console_inputs.len(), "Expected {num_inputs} inputs, found {}", console_inputs.len());

        // Initialize the registers.
        let call_stack = CallStack::PackageRun(vec![], PrivateKey::new(&mut rand::thread_rng())?, Default::default());
        let mut registers = Registers::<N, A>::new(call_stack, register_types);
        lap!(timer, "Initialize the registers");

        // Ensure the circuit environment is clean.
        A::reset();

        // Inject the circuit inputs.
        let mut circuit_inputs = Vec::with_capacity(console_inputs.len());
        // Iterate over the console inputs.
        for input in console_inputs {
            // Inject the input as `Mode::Public`.
            let input = <circuit::Value<A> as circuit::Inject>::new(Mode::Public, input);
            // Store the input.
            circuit_inputs.push(input);
        }
        lap!(timer, "Inject the inputs");

        // Store the inputs into the registers.
        function.inputs().iter().map(|i| i.register()).zip_eq(&circuit_inputs).try_for_each(|(register, input)| {
            // Assign the circuit input to the register.
            registers.store_circuit(&self.stack, register, input.clone())
        })?;
        lap!(timer, "Store the inputs");

        // Execute the instructions.
        for instruction in function.instructions() {
            // If the execution fails, bail and return the error.
            if let Err(error) = instruction.execute(&self.stack, &mut registers) {
                bail!("Failed to execute instruction ({instruction}): {error}");
            }

            #[cfg(feature = "debug")]
            {
                use colored::Colorize;

                let is_satisfied = A::is_satisfied();
                println!(
                    "Executing instruction ({instruction}) ({})",
                    if is_satisfied { "✅".green() } else { "❌".red() }
                );
                if !is_satisfied {
                    for operand in instruction.operands() {
                        use synthesizer_program::RegistersLoadCircuit;
                        let value = registers.load_circuit(&self.stack, operand)?;
                        println!("    {operand} = {}", value.eject_value());
                    }
                }
            }
        }
        lap!(timer, "Execute the instructions");

        #[cfg(debug_assertions)]
        log_circuit::<N, A, _>(function_name.to_string());

        // If the circuit is empty or not satisfied, then throw an error.
        ensure!(
            A::num_constraints() > 0 && A::is_satisfied(),
            "'{}/{function_name}' is not satisfied on the given inputs.",
            self.stack.program_id(),
        );
        lap!(timer, "Ensure the circuit is satisfied");

        // Eject the R1CS and reset the circuit.
        let r1cs = A::eject_r1cs_and_reset();
        finish!(timer, "Eject the circuit assignment and reset the circuit");

        Ok(r1cs)
    }
}

/// Prints the current state of the circuit.
#[cfg(debug_assertions)]
pub(crate) fn log_circuit<N: Network, A: circuit::Aleo<Network = N>, S: Into<String>>(scope: S) {
    use colored::Colorize;

    // Determine if the circuit is satisfied.
    let is_satisfied = if A::is_satisfied() { "✅".green() } else { "❌".red() };
    // Determine the count.
    let (num_constant, num_public, num_private, num_constraints, num_nonzeros) = A::count();

    // Print the log.
    println!(
        "{is_satisfied} {:width$} (Constant: {num_constant}, Public: {num_public}, Private: {num_private}, Constraints: {num_constraints}, NonZeros: {num_nonzeros:?})",
        scope.into().bold(),
        width = 20
    );
}
