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

mod input;
use input::*;

mod instruction;
pub(crate) use instruction::*;

mod output;
use output::*;

mod register;
pub use register::Register;

mod registers;
use registers::{RegisterType, Registers};

mod bytes;
mod parse;

use crate::{
    function::{Input, Output},
    Identifier,
    LiteralType,
    Plaintext,
    PlaintextType,
    Program,
    Sanitizer,
    Value,
    ValueType,
};
use snarkvm_console_network::prelude::*;
use snarkvm_utilities::{
    error,
    io::{Read, Result as IoResult, Write},
    FromBytes,
    ToBytes,
};

use indexmap::{IndexMap, IndexSet};

#[derive(Clone, PartialEq, Eq)]
pub struct Function<N: Network> {
    /// The name of the function.
    name: Identifier<N>,
    /// The input statements, added in order of the input registers.
    /// Input assignments are ensured to match the ordering of the input statements.
    inputs: IndexSet<Input<N>>,
    /// The instructions, in order of execution.
    instructions: Vec<Instruction<N>>,
    /// The output statements, in order of the desired output.
    /// There is no expectation that the output registers are in any ordering.
    outputs: IndexSet<Output<N>>,
}

impl<N: Network> Function<N> {
    /// Initializes a new function with the given name.
    pub fn new(name: Identifier<N>) -> Self {
        Self { name, inputs: IndexSet::new(), instructions: Vec::new(), outputs: IndexSet::new() }
    }

    /// Returns the name of the function.
    pub fn name(&self) -> &Identifier<N> {
        &self.name
    }

    /// Returns the function inputs.
    pub const fn inputs(&self) -> &IndexSet<Input<N>> {
        &self.inputs
    }

    /// Returns the function instructions.
    pub fn instructions(&self) -> &[Instruction<N>] {
        &self.instructions
    }

    /// Returns the function outputs.
    pub const fn outputs(&self) -> &IndexSet<Output<N>> {
        &self.outputs
    }
}

impl<N: Network> Function<N> {
    /// Adds the input statement to the function.
    ///
    /// # Errors
    /// This method will halt if there are instructions or output statements already.
    /// This method will halt if the maximum number of inputs has been reached.
    /// This method will halt if the input statement was previously added.
    #[inline]
    fn add_input(&mut self, input: Input<N>) -> Result<()> {
        // Ensure there are no instructions or output statements in memory.
        ensure!(self.instructions.is_empty(), "Cannot add inputs after instructions have been added");
        ensure!(self.outputs.is_empty(), "Cannot add inputs after outputs have been added");

        // Ensure the maximum number of inputs has not been exceeded.
        ensure!(self.inputs.len() <= N::MAX_FUNCTION_INPUTS, "Cannot add more than {} inputs", N::MAX_FUNCTION_INPUTS);
        // Ensure the input statement was not previously added.
        ensure!(!self.inputs.contains(&input), "Cannot add duplicate input statement");

        // Insert the input statement.
        self.inputs.insert(input);
        Ok(())
    }

    /// Adds the given instruction to the function.
    ///
    /// # Errors
    /// This method will halt if there are no input statements in memory.
    /// This method will halt if the maximum number of instructions has been reached.
    #[inline]
    pub fn add_instruction(&mut self, instruction: Instruction<N>) -> Result<()> {
        // Ensure there are input statements in memory.
        ensure!(!self.inputs.is_empty(), "Cannot add instructions before inputs have been added");

        // Ensure the maximum number of instructions has not been exceeded.
        ensure!(
            self.instructions.len() <= N::MAX_FUNCTION_INSTRUCTIONS,
            "Cannot add more than {} instructions",
            N::MAX_FUNCTION_INSTRUCTIONS
        );

        // Insert the instruction.
        self.instructions.push(instruction);
        Ok(())
    }

    /// Adds the output statement to the function.
    ///
    /// # Errors
    /// This method will halt if there are no input statements or instructions in memory.
    /// This method will halt if the maximum number of outputs has been reached.
    #[inline]
    fn add_output(&mut self, output: Output<N>) -> Result<()> {
        // Ensure there are input statements and instructions in memory.
        ensure!(!self.inputs.is_empty(), "Cannot add outputs before inputs have been added");
        ensure!(!self.instructions.is_empty(), "Cannot add outputs before instructions have been added");

        // Ensure the maximum number of outputs has not been exceeded.
        ensure!(
            self.outputs.len() <= N::MAX_FUNCTION_OUTPUTS,
            "Cannot add more than {} outputs",
            N::MAX_FUNCTION_OUTPUTS
        );

        // Insert the output statement.
        self.outputs.insert(output);
        Ok(())
    }

    // /// Evaluates the function on the given inputs.
    // ///
    // /// # Errors
    // /// This method will halt if there are no input statements or instructions in memory.
    // /// This method will halt if any registers are already assigned.
    // /// This method will halt if the given inputs are not the same length as the input statements.
    // #[inline]
    // pub fn evaluate(&self, program: &Program<N>, inputs: &[Plaintext<N>]) -> Result<Vec<Value<N, Plaintext<N>>>> {
    //     // Ensure there are input statements and instructions in memory.
    //     ensure!(!self.inputs.is_empty(), "Cannot evaluate a function without input statements");
    //     ensure!(!self.instructions.is_empty(), "Cannot evaluate a function without instructions");
    //
    //     // Ensure the number of inputs matches the number of input statements.
    //     ensure!(self.inputs.len() == inputs.len(), "Expected {} inputs, but given {}", self.inputs.len(), inputs.len());
    //
    //     // Initialize a registers map to store the values for destination registers.
    //     let mut registers = Registers::<N>::new(self.registers.clone(), inputs)?;
    //
    //     // Assign the inputs and ensure they matches the input statements.
    //     self.assign_inputs(inputs);
    //
    //     // Evaluate the instructions.
    //     for instruction in self.instructions.iter() {
    //         instruction.evaluate(&self.registers);
    //     }
    //
    //     // Load the outputs.
    //     let mut outputs = Vec::with_capacity(self.outputs.len());
    //     for output in self.outputs.iter() {
    //         // Load the value from the output register.
    //         let register = output.register();
    //         let value = self.registers.load(register);
    //
    //         // TODO (howardwu): When handling the TODO below, relax this to exclude checking the mode.
    //         // Ensure the output plaintext type matches the annotation.
    //         if &value.annotation() != output.annotation() {
    //             P::halt(format!("Output \'{register}\' has an incorrect annotation of {}", value.annotation()))
    //         }
    //
    //         // TODO (howardwu): When handling the TODO below, relax this to exclude checking the mode.
    //         // If the output annotation is a definition, ensure the output value matches the definition.
    //         if let Annotation::Definition(definition_name) = output.annotation() {
    //             // Retrieve the definition from the program.
    //             match P::get_definition(definition_name) {
    //                 // Ensure the value matches its expected definition.
    //                 Some(definition) => {
    //                     if !definition.matches(&value) {
    //                         P::halt(format!("Output \'{register}\' does not match \'{definition_name}\'"))
    //                     }
    //                 }
    //                 None => P::halt("Output \'{register}\' references a non-existent definition"),
    //             }
    //         }
    //
    //         // TODO (howardwu): Add encryption against the caller's address for all private literals,
    //         //  and inject the ciphertext as Mode::Public, along with a constraint enforcing equality.
    //         //  For constant outputs, add an assert_eq on the register value - if it's constant,
    //         //  the constraint will automatically be discarded, and if it's not, the constraint will
    //         //  ensure the output register's value matches the newly-assigned hardcoded constant.
    //         // // If the value contains any public literals, assign a new public variable for the public literal,
    //         // // and add a constraint to enforce equality of the value.
    //         // match &value {
    //         //     Value::Literal(literal) => {
    //         //         if literal.is_public() {
    //         //             let public_literal = Literal::new(Mode::Public, literal.eject_value());
    //         //             P::Environment::assert_eq(literal, public_literal);
    //         //         }
    //         //     }
    //         //     Value::Definition(_, members) => {
    //         //         for member in members.iter() {
    //         //             if member.is_public() {
    //         //                 let public_literal = Literal::new(Mode::Public, member.eject_value());
    //         //                 P::Environment::assert_eq(member, public_literal);
    //         //             }
    //         //         }
    //         //     }
    //         // }
    //
    //         // Insert the value into the outputs.
    //         outputs.push(value);
    //     }
    //
    //     // Clear the register assignments.
    //     self.registers.clear_assignments();
    //
    //     outputs
    // }
}

impl<N: Network> TypeName for Function<N> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "function"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    //     #[test]
    //     fn test_function_evaluate() {
    //         let function = Function::<CurrentNetwork>::from_str(
    //             r"
    // function foo:
    //     input r0 as field.public;
    //     input r1 as field.private;
    //     add r0 r1 into r2;
    //     output r2 as field.private;
    // ",
    //         );
    //         let first = Value::<CurrentNetwork>::from_str("2field.public");
    //         let second = Value::from_str("3field.private");
    //
    //         // Run the function.
    //         let expected = Value::<CurrentNetwork>::from_str("5field.private");
    //         let candidate = function.evaluate(&[first.clone(), second.clone()]);
    //         assert_eq!(expected.to_string(), candidate[0].to_string());
    //
    //         // Re-run to ensure state continues to work.
    //         let expected = Value::<CurrentNetwork>::from_str("5field.private");
    //         let candidate = function.evaluate(&[first, second]);
    //         assert_eq!(expected.to_string(), candidate[0].to_string());
    //     }
}
