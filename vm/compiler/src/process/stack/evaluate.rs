// Copyright (C) 2019-2022 Aleo Systems Inc.
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

impl<N: Network> Stack<N> {
    /// Evaluates a program closure on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn evaluate_closure<A: circuit::Aleo<Network = N>>(
        &self,
        closure: &Closure<N>,
        inputs: &[Value<N>],
    ) -> Result<Vec<Value<N>>> {
        // Ensure the number of inputs matches the number of input statements.
        if closure.inputs().len() != inputs.len() {
            bail!("Expected {} inputs, found {}", closure.inputs().len(), inputs.len())
        }

        // Initialize the registers.
        let mut registers =
            Registers::<N, A>::new(CallStack::Evaluate, self.get_register_types(closure.name())?.clone());

        // Store the inputs.
        closure.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(|(register, input)| {
            // Assign the input value to the register.
            registers.store(self, register, input.clone())
        })?;

        // Evaluate the instructions.
        for instruction in closure.instructions() {
            // If the evaluation fails, bail and return the error.
            if let Err(error) = instruction.evaluate(self, &mut registers) {
                bail!("Failed to evaluate instruction ({instruction}): {error}");
            }
        }

        // Load the outputs.
        let outputs = closure.outputs().iter().map(|output| {
            // Retrieve the stack value from the register.
            registers.load(self, &Operand::Register(output.register().clone()))
        });

        outputs.collect()
    }

    /// Evaluates a program function on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn evaluate_function<A: circuit::Aleo<Network = N>>(
        &self,
        function: &Function<N>,
        inputs: &[Value<N>],
    ) -> Result<Vec<Value<N>>> {
        // Ensure the number of inputs matches.
        if function.inputs().len() != inputs.len() {
            bail!(
                "Function '{}' in the program '{}' expects {} inputs, but {} were provided.",
                function.name(),
                self.program.id(),
                function.inputs().len(),
                inputs.len()
            )
        }

        // Initialize the registers.
        let mut registers =
            Registers::<N, A>::new(CallStack::Evaluate, self.get_register_types(function.name())?.clone());

        // Store the inputs.
        function.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(|(register, input)| {
            // Assign the input value to the register.
            registers.store(self, register, input.clone())
        })?;

        // Evaluate the instructions.
        for instruction in function.instructions() {
            // If the evaluation fails, bail and return the error.
            if let Err(error) = instruction.evaluate(self, &mut registers) {
                bail!("Failed to evaluate instruction ({instruction}): {error}");
            }
        }

        // Load the outputs.
        let outputs = function.outputs().iter().map(|output| {
            // Retrieve the stack value from the register.
            registers.load(self, &Operand::Register(output.register().clone()))
        });

        outputs.collect()
    }
}
