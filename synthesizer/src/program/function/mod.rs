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

mod input;
use input::*;

mod output;
use output::*;

mod bytes;
mod parse;

use crate::{
    program::finalize::{Finalize, FinalizeCommand},
    Instruction,
};
use console::{
    network::prelude::*,
    program::{Identifier, Register, ValueType},
};

use indexmap::IndexSet;

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
    outputs: IndexSet<Output<N>>,
    /// The optional finalize command and logic.
    finalize: Option<(FinalizeCommand<N>, Finalize<N>)>,
}

impl<N: Network> Function<N> {
    /// Initializes a new function with the given name.
    pub fn new(name: Identifier<N>) -> Self {
        Self { name, inputs: IndexSet::new(), instructions: Vec::new(), outputs: IndexSet::new(), finalize: None }
    }

    /// Returns the name of the function.
    pub const fn name(&self) -> &Identifier<N> {
        &self.name
    }

    /// Returns the function inputs.
    pub const fn inputs(&self) -> &IndexSet<Input<N>> {
        &self.inputs
    }

    /// Returns the function input types.
    pub fn input_types(&self) -> Vec<ValueType<N>> {
        self.inputs.iter().map(|input| *input.value_type()).collect()
    }

    /// Returns the function instructions.
    pub fn instructions(&self) -> &[Instruction<N>] {
        &self.instructions
    }

    /// Returns the function outputs.
    pub const fn outputs(&self) -> &IndexSet<Output<N>> {
        &self.outputs
    }

    /// Returns the function output types.
    pub fn output_types(&self) -> Vec<ValueType<N>> {
        self.outputs.iter().map(|output| *output.value_type()).collect()
    }

    /// Returns the function finalize logic.
    pub const fn finalize(&self) -> Option<&(FinalizeCommand<N>, Finalize<N>)> {
        self.finalize.as_ref()
    }

    /// Returns the function finalize command.
    pub fn finalize_command(&self) -> Option<&FinalizeCommand<N>> {
        self.finalize.as_ref().map(|(command, _)| command)
    }

    /// Returns the function finalize logic.
    pub fn finalize_logic(&self) -> Option<&Finalize<N>> {
        self.finalize.as_ref().map(|(_, finalize)| finalize)
    }
}

impl<N: Network> Function<N> {
    /// Adds the input statement to the function.
    ///
    /// # Errors
    /// This method will halt if there are instructions or output statements already.
    /// This method will halt if the maximum number of inputs has been reached.
    /// This method will halt if the input statement was previously added.
    /// This method will halt if a finalize command has been added.
    #[inline]
    fn add_input(&mut self, input: Input<N>) -> Result<()> {
        // Ensure there are no instructions or output statements in memory.
        ensure!(self.instructions.is_empty(), "Cannot add inputs after instructions have been added");
        ensure!(self.outputs.is_empty(), "Cannot add inputs after outputs have been added");

        // Ensure the maximum number of inputs has not been exceeded.
        ensure!(self.inputs.len() < N::MAX_INPUTS, "Cannot add more than {} inputs", N::MAX_INPUTS);
        // Ensure the input statement was not previously added.
        ensure!(!self.inputs.contains(&input), "Cannot add duplicate input statement");

        // Ensure a finalize command has not been added.
        ensure!(self.finalize.is_none(), "Cannot add instructions after finalize command has been added");

        // Ensure the input register is a locator.
        ensure!(matches!(input.register(), Register::Locator(..)), "Input register must be a locator");

        // Insert the input statement.
        self.inputs.insert(input);
        Ok(())
    }

    /// Adds the given instruction to the function.
    ///
    /// # Errors
    /// This method will halt if there are output statements already.
    /// This method will halt if the maximum number of instructions has been reached.
    /// This method will halt if a finalize command has been added.
    #[inline]
    pub fn add_instruction(&mut self, instruction: Instruction<N>) -> Result<()> {
        // Ensure that there are no output statements in memory.
        ensure!(self.outputs.is_empty(), "Cannot add instructions after outputs have been added");

        // Ensure the maximum number of instructions has not been exceeded.
        ensure!(
            self.instructions.len() < N::MAX_INSTRUCTIONS,
            "Cannot add more than {} instructions",
            N::MAX_INSTRUCTIONS
        );

        // Ensure a finalize command has not been added.
        ensure!(self.finalize.is_none(), "Cannot add instructions after finalize command has been added");

        // Ensure the destination register is a locator.
        for register in instruction.destinations() {
            ensure!(matches!(register, Register::Locator(..)), "Destination register must be a locator");
        }

        // Insert the instruction.
        self.instructions.push(instruction);
        Ok(())
    }

    /// Adds the output statement to the function.
    ///
    /// # Errors
    /// This method will halt if the maximum number of outputs has been reached.
    /// This method will halt if a finalize command has been added.
    #[inline]
    fn add_output(&mut self, output: Output<N>) -> Result<()> {
        // Ensure the maximum number of outputs has not been exceeded.
        ensure!(self.outputs.len() < N::MAX_OUTPUTS, "Cannot add more than {} outputs", N::MAX_OUTPUTS);
        // Ensure the output statement was not previously added.
        ensure!(!self.outputs.contains(&output), "Cannot add duplicate output statement");

        // Ensure a finalize command has not been added.
        ensure!(self.finalize.is_none(), "Cannot add instructions after finalize command has been added");

        // Insert the output statement.
        self.outputs.insert(output);
        Ok(())
    }

    /// Adds the finalize scope to the function.
    ///
    /// # Errors
    /// This method will halt if a finalize scope has already been added.
    /// This method will halt if name in the finalize scope does not match the function name.
    /// This method will halt if the maximum number of finalize inputs has been reached.
    /// This method will halt if the number of finalize operands does not match the number of finalize inputs.
    #[inline]
    fn add_finalize(&mut self, command: FinalizeCommand<N>, finalize: Finalize<N>) -> Result<()> {
        // Ensure there is no finalize scope in memory.
        ensure!(self.finalize.is_none(), "Cannot add multiple finalize scopes to function '{}'", self.name);
        // Ensure the finalize scope name matches the function name.
        ensure!(*finalize.name() == self.name, "Finalize scope name must match function name '{}'", self.name);
        // Ensure the number of finalize inputs has not been exceeded.
        ensure!(finalize.inputs().len() <= N::MAX_INPUTS, "Cannot add more than {} inputs to finalize", N::MAX_INPUTS);
        // Ensure the finalize command has the same number of operands as the finalize inputs.
        ensure!(
            command.operands().len() == finalize.inputs().len(),
            "The 'finalize' command has {} operands, but 'finalize' takes {} inputs",
            command.operands().len(),
            finalize.inputs().len()
        );

        // Insert the finalize scope.
        self.finalize = Some((command, finalize));
        Ok(())
    }
}

impl<N: Network> TypeName for Function<N> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "function"
    }
}
