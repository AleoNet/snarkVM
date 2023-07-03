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

mod input;
use input::*;

mod output;
use output::*;

mod bytes;
mod parse;

use crate::{
    finalize::FinalizeCore,
    traits::{CommandTrait, FinalizeCommandTrait, InstructionTrait},
};
use console::{
    network::prelude::*,
    program::{Identifier, Register, ValueType},
};

use indexmap::IndexSet;

#[derive(Clone, PartialEq, Eq)]
pub struct FunctionCore<N: Network, Instruction: InstructionTrait<N>, Command: CommandTrait<N>> {
    /// The name of the function.
    name: Identifier<N>,
    /// The input statements, added in order of the input registers.
    /// Input assignments are ensured to match the ordering of the input statements.
    inputs: IndexSet<Input<N>>,
    /// The instructions, in order of execution.
    instructions: Vec<Instruction>,
    /// The output statements, in order of the desired output.
    outputs: IndexSet<Output<N>>,
    /// The optional finalize command and logic.
    finalize: Option<(Command::FinalizeCommand, FinalizeCore<N, Command>)>,
}

impl<N: Network, Instruction: InstructionTrait<N>, Command: CommandTrait<N>> FunctionCore<N, Instruction, Command> {
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
    pub fn instructions(&self) -> &[Instruction] {
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
    pub const fn finalize(&self) -> Option<&(Command::FinalizeCommand, FinalizeCore<N, Command>)> {
        self.finalize.as_ref()
    }

    /// Returns the function finalize command.
    pub fn finalize_command(&self) -> Option<&Command::FinalizeCommand> {
        self.finalize.as_ref().map(|(command, _)| command)
    }

    /// Returns the function finalize logic.
    pub fn finalize_logic(&self) -> Option<&FinalizeCore<N, Command>> {
        self.finalize.as_ref().map(|(_, finalize)| finalize)
    }
}

impl<N: Network, Instruction: InstructionTrait<N>, Command: CommandTrait<N>> FunctionCore<N, Instruction, Command> {
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
    pub fn add_instruction(&mut self, instruction: Instruction) -> Result<()> {
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
    fn add_finalize(&mut self, command: Command::FinalizeCommand, finalize: FinalizeCore<N, Command>) -> Result<()> {
        // Ensure there is no finalize scope in memory.
        ensure!(self.finalize.is_none(), "Cannot add multiple finalize scopes to function '{}'", self.name);
        // Ensure the finalize scope name matches the function name.
        ensure!(*finalize.name() == self.name, "Finalize scope name must match function name '{}'", self.name);
        // Ensure the number of finalize inputs has not been exceeded.
        ensure!(finalize.inputs().len() <= N::MAX_INPUTS, "Cannot add more than {} inputs to finalize", N::MAX_INPUTS);
        // Ensure the finalize command has the same number of operands as the finalize inputs.
        ensure!(
            command.num_operands() == finalize.inputs().len(),
            "The 'finalize' command has {} operands, but 'finalize' takes {} inputs",
            command.num_operands(),
            finalize.inputs().len()
        );

        // Insert the finalize scope.
        self.finalize = Some((command, finalize));
        Ok(())
    }
}

impl<N: Network, Instruction: InstructionTrait<N>, Command: CommandTrait<N>> TypeName
    for FunctionCore<N, Instruction, Command>
{
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "function"
    }
}
