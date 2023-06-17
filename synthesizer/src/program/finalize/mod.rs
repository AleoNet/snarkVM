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

mod bytes;
mod parse;

use console::{
    network::prelude::*,
    program::{Identifier, PlaintextType, Register},
};

use indexmap::IndexSet;
use std::collections::HashMap;

pub trait FinalizeCommandTrait: Clone + PartialEq + Eq + Parser + FromBytes + ToBytes {
    /// Returns the number of operands.
    fn num_operands(&self) -> usize;
}

pub trait CommandTrait<N: Network>: Clone + Parser + FromBytes + ToBytes {
    type FinalizeCommand: FinalizeCommandTrait;
}

#[derive(Clone, PartialEq, Eq)]
pub struct FinalizeCore<N: Network, Command: CommandTrait<N>> {
    /// The name of the associated function.
    name: Identifier<N>,
    /// The input statements, added in order of the input registers.
    /// Input assignments are ensured to match the ordering of the input statements.
    inputs: IndexSet<Input<N>>,
    /// The commands, in order of execution.
    commands: Vec<Command>,
    /// The number of write commands.
    num_writes: u16,
    /// A mapping from `Position`s to their index in `commands`.
    positions: HashMap<Identifier<N>, usize>,
}

impl<N: Network, Command: CommandTrait<N>> FinalizeCore<N, Command> {
    /// Initializes a new finalize with the given name.
    pub fn new(name: Identifier<N>) -> Self {
        Self { name, inputs: IndexSet::new(), commands: Vec::new(), num_writes: 0, positions: HashMap::new() }
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
    pub fn input_types(&self) -> Vec<PlaintextType<N>> {
        self.inputs.iter().map(|input| *input.plaintext_type()).collect()
    }

    /// Returns the finalize commands.
    pub fn commands(&self) -> &[Command] {
        &self.commands
    }

    /// Returns the number of write commands.
    pub const fn num_writes(&self) -> u16 {
        self.num_writes
    }

    /// Returns the mapping of `Position`s to their index in `commands`.
    pub const fn positions(&self) -> &HashMap<Identifier<N>, usize> {
        &self.positions
    }
}

impl<N: Network, Command: CommandTrait<N>> FinalizeCore<N, Command> {
    /// Adds the input statement to finalize.
    ///
    /// # Errors
    /// This method will halt if a command was previously added.
    /// This method will halt if the maximum number of inputs has been reached.
    /// This method will halt if the input statement was previously added.
    #[inline]
    fn add_input(&mut self, input: Input<N>) -> Result<()> {
        // Ensure there are no commands in memory.
        ensure!(self.commands.is_empty(), "Cannot add inputs after commands have been added");

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
    pub fn add_command(&mut self, command: Command) -> Result<()> {
        // Ensure the maximum number of commands has not been exceeded.
        ensure!(self.commands.len() < N::MAX_COMMANDS, "Cannot add more than {} commands", N::MAX_COMMANDS);
        // Ensure the number of write commands has not been exceeded.
        ensure!(self.num_writes < N::MAX_WRITES, "Cannot add more than {} 'set' commands", N::MAX_WRITES);

        // // Perform additional checks on the command.
        // match &command {
        //     Command::Instruction(instruction) => {
        //         match instruction {
        //             // Ensure the instruction is not a `call`.
        //             Instruction::Call(_) => bail!("Forbidden operation: Finalize cannot invoke a 'call'"),
        //             // Ensure the instruction is not a `cast` to a record.
        //             Instruction::Cast(cast) if !matches!(cast.register_type(), &RegisterType::Plaintext(_)) => {
        //                 bail!("Forbidden operation: Finalize cannot cast to a record")
        //             }
        //             _ => {}
        //         }
        //         // Ensure the destination register is a locator.
        //         for register in instruction.destinations() {
        //             ensure!(matches!(register, Register::Locator(..)), "Destination register must be a locator");
        //         }
        //     }
        //     Command::Contains(contains) => {
        //         // Ensure the destination register is a locator.
        //         ensure!(
        //             matches!(contains.destination(), Register::Locator(..)),
        //             "Destination register must be a locator"
        //         );
        //     }
        //     Command::Get(get) => {
        //         // Ensure the destination register is a locator.
        //         ensure!(matches!(get.destination(), Register::Locator(..)), "Destination register must be a locator");
        //     }
        //     Command::GetOrUse(get_or_use) => {
        //         // Ensure the destination register is a locator.
        //         ensure!(
        //             matches!(get_or_use.destination(), Register::Locator(..)),
        //             "Destination register must be a locator"
        //         );
        //     }
        //     Command::RandChaCha(rand_chacha) => {
        //         // Ensure the destination register is a locator.
        //         ensure!(
        //             matches!(rand_chacha.destination(), Register::Locator(..)),
        //             "Destination register must be a locator"
        //         );
        //     }
        //     Command::Remove(_) => {
        //         // Increment the number of write commands.
        //         self.num_writes += 1;
        //     }
        //     Command::Set(_) => {
        //         // Increment the number of write commands.
        //         self.num_writes += 1;
        //     }
        //     Command::BranchEq(branch) => {
        //         // Ensure that the position referenced by the branch is **not** yet defined.
        //         // This ensures that the branch **only** jumps forward.
        //         ensure!(
        //             self.positions.get(branch.position()).is_none(),
        //             "Cannot branch to an earlier position '{}' in the program",
        //             branch.position()
        //         );
        //     }
        //     Command::BranchNeq(branch) => {
        //         // Ensure that the position referenced by the branch is **not** yet defined.
        //         // This ensures that the branch **only** jumps forward.
        //         ensure!(
        //             self.positions.get(branch.position()).is_none(),
        //             "Cannot branch to an earlier position '{}' in the program",
        //             branch.position()
        //         );
        //     }
        //     Command::Position(position) => {
        //         // Ensure that the `Position` is not already defined.
        //         ensure!(
        //             self.positions.get(position.name()).is_none(),
        //             "The position `{}` is not unique",
        //             position.name()
        //         );
        //         // Track the index of the `Position`.
        //         self.positions.insert(*position.name(), self.commands.len());
        //     }
        // }

        // Insert the command.
        self.commands.push(command);
        Ok(())
    }
}

impl<N: Network, Command: CommandTrait<N>> TypeName for FinalizeCore<N, Command> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "finalize"
    }
}
