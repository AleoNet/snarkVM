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

mod command;
pub use command::*;

mod input;
use input::*;

mod output;
use output::*;

mod bytes;
mod parse;

use crate::Instruction;
use console::{
    network::prelude::*,
    program::{FinalizeType, Identifier, Register},
};

use indexmap::IndexSet;

#[derive(Clone, PartialEq, Eq)]
pub struct Finalize<N: Network> {
    /// The name of the associated function.
    name: Identifier<N>,
    /// The input statements, added in order of the input registers.
    /// Input assignments are ensured to match the ordering of the input statements.
    inputs: IndexSet<Input<N>>,
    /// The commands, in order of execution.
    commands: Vec<Command<N>>,
    /// The output statements, in order of the desired output.
    outputs: IndexSet<Output<N>>,
}

impl<N: Network> Finalize<N> {
    /// Initializes a new finalize with the given name.
    pub fn new(name: Identifier<N>) -> Self {
        Self { name, inputs: IndexSet::new(), commands: Vec::new(), outputs: IndexSet::new() }
    }

    /// Returns the name of the associated function.
    pub const fn name(&self) -> &Identifier<N> {
        &self.name
    }

    /// Returns the finalize inputs.
    pub const fn inputs(&self) -> &IndexSet<Input<N>> {
        &self.inputs
    }

    /// Returns the finalize input types.
    pub fn input_types(&self) -> Vec<FinalizeType<N>> {
        self.inputs.iter().map(|input| *input.finalize_type()).collect()
    }

    /// Returns the finalize commands.
    pub fn commands(&self) -> &[Command<N>] {
        &self.commands
    }

    /// Returns the finalize outputs.
    pub const fn outputs(&self) -> &IndexSet<Output<N>> {
        &self.outputs
    }

    /// Returns the finalize output types.
    pub fn output_types(&self) -> Vec<FinalizeType<N>> {
        self.outputs.iter().map(|output| *output.finalize_type()).collect()
    }
}

impl<N: Network> Finalize<N> {
    /// Adds the input statement to finalize.
    ///
    /// # Errors
    /// This method will halt if there are commands or output statements already.
    /// This method will halt if the maximum number of inputs has been reached.
    /// This method will halt if the input statement was previously added.
    #[inline]
    fn add_input(&mut self, input: Input<N>) -> Result<()> {
        // Ensure there are no commands or output statements in memory.
        ensure!(self.commands.is_empty(), "Cannot add inputs after commands have been added");
        ensure!(self.outputs.is_empty(), "Cannot add inputs after outputs have been added");

        // Ensure the maximum number of inputs has not been exceeded.
        ensure!(self.inputs.len() <= N::MAX_INPUTS, "Cannot add more than {} inputs", N::MAX_INPUTS);
        // Ensure the input statement was not previously added.
        ensure!(!self.inputs.contains(&input), "Cannot add duplicate input statement");

        // Ensure the input register is a locator.
        ensure!(matches!(input.register(), Register::Locator(..)), "Input register must be a locator");

        // Insert the input statement.
        self.inputs.insert(input);
        Ok(())
    }

    /// Adds the given command to finalize.
    ///
    /// # Errors
    /// This method will halt if the maximum number of commands has been reached.
    #[inline]
    pub fn add_command(&mut self, command: Command<N>) -> Result<()> {
        // Ensure the maximum number of commands has not been exceeded.
        ensure!(self.commands.len() <= N::MAX_COMMANDS, "Cannot add more than {} commands", N::MAX_COMMANDS);

        // If the command is an instruction, perform additional checks.
        if let Command::Instruction(instruction) = &command {
            // Ensure the instruction is not a `call`.
            ensure!(
                !matches!(instruction, Instruction::Call(..)),
                "Forbidden operation: Finalize cannot invoke a 'call'"
            );

            // Ensure the destination register is a locator.
            for register in instruction.destinations() {
                ensure!(matches!(register, Register::Locator(..)), "Destination register must be a locator");
            }
        }

        // Insert the command.
        self.commands.push(command);
        Ok(())
    }

    /// Adds the output statement to finalize.
    ///
    /// # Errors
    /// This method will halt if there are no commands in memory.
    /// This method will halt if the maximum number of outputs has been reached.
    #[inline]
    fn add_output(&mut self, output: Output<N>) -> Result<()> {
        // Ensure there are commands in memory.
        ensure!(!self.commands.is_empty(), "Cannot add outputs before commands have been added");

        // Ensure the maximum number of outputs has not been exceeded.
        ensure!(self.outputs.len() <= N::MAX_OUTPUTS, "Cannot add more than {} outputs", N::MAX_OUTPUTS);
        // Ensure the output statement was not previously added.
        ensure!(!self.outputs.contains(&output), "Cannot add duplicate output statement");

        // Insert the output statement.
        self.outputs.insert(output);
        Ok(())
    }
}

impl<N: Network> TypeName for Finalize<N> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "finalize"
    }
}
