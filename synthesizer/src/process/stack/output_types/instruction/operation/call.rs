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

impl<N: Network> Stack<N> {
    /// Returns `true` if the call instruction is a function call.
    #[inline]
    pub fn is_function_call(&self, call: &Call<N>) -> Result<bool> {
        match call.operator() {
            // Check if the locator is for a function.
            CallOperator::Locator(locator) => {
                // Retrieve the program.
                let program = self.get_external_program(locator.program_id())?;
                // Check if the resource is a function.
                Ok(program.contains_function(locator.resource()))
            }
            // Check if the resource is a function.
            CallOperator::Resource(resource) => Ok(self.program().contains_function(resource)),
        }
    }

    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn output_types(&self, call: &Call<N>, input_types: &[RegisterType<N>]) -> Result<Vec<RegisterType<N>>> {
        // Retrieve the program and resource.
        let (is_external, program, resource) = match &self.operator {
            // Retrieve the program and resource from the locator.
            CallOperator::Locator(locator) => {
                (true, stack.get_external_program(locator.program_id())?, locator.resource())
            }
            CallOperator::Resource(resource) => {
                // TODO (howardwu): Revisit this decision to forbid calling internal functions. A record cannot be spent again.
                //  But there are legitimate uses for passing a record through to an internal function.
                //  We could invoke the internal function without a state transition, but need to match visibility.
                if stack.program().contains_function(resource) {
                    bail!("Cannot call '{resource}'. Use a closure ('closure {resource}:') instead.")
                }

                (false, stack.program(), resource)
            }
        };

        // If the operator is a closure, retrieve the closure and compute the output types.
        if let Ok(closure) = program.get_closure(resource) {
            // Ensure the number of operands matches the number of input statements.
            if closure.inputs().len() != self.operands.len() {
                bail!("Expected {} inputs, found {}", closure.inputs().len(), self.operands.len())
            }
            // Ensure the number of inputs matches the number of input statements.
            if closure.inputs().len() != input_types.len() {
                bail!("Expected {} input types, found {}", closure.inputs().len(), input_types.len())
            }
            // Ensure the number of destinations matches the number of output statements.
            if closure.outputs().len() != self.destinations.len() {
                bail!("Expected {} outputs, found {}", closure.outputs().len(), self.destinations.len())
            }
            // Return the output register types.
            Ok(closure.outputs().iter().map(|output| *output.register_type()).collect())
        }
        // If the operator is a function, retrieve the function and compute the output types.
        else if let Ok(function) = program.get_function(resource) {
            // Ensure the number of operands matches the number of input statements.
            if function.inputs().len() != self.operands.len() {
                bail!("Expected {} inputs, found {}", function.inputs().len(), self.operands.len())
            }
            // Ensure the number of inputs matches the number of input statements.
            if function.inputs().len() != input_types.len() {
                bail!("Expected {} input types, found {}", function.inputs().len(), input_types.len())
            }
            // Ensure the number of destinations matches the number of output statements.
            if function.outputs().len() != self.destinations.len() {
                bail!("Expected {} outputs, found {}", function.outputs().len(), self.destinations.len())
            }
            // Return the output register types.
            function
                .output_types()
                .into_iter()
                .map(|output_type| match (is_external, output_type) {
                    // If the output is a record and the function is external, return the external record type.
                    (true, ValueType::Record(record_name)) => Ok(RegisterType::ExternalRecord(Locator::from_str(
                        &format!("{}/{}", program.id(), record_name),
                    )?)),
                    // Else, return the register type.
                    (_, _) => Ok(RegisterType::from(output_type)),
                })
                .collect::<Result<Vec<_>>>()
        }
        // Else, throw an error.
        else {
            bail!("Call operator '{}' is invalid or unsupported.", self.operator)
        }
    }
}
