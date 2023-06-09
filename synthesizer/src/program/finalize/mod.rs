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

mod command;
pub use command::*;

mod input;
use input::*;

mod bytes;
mod parse;

use crate::Instruction;
use console::{
    network::prelude::*,
    program::{Identifier, PlaintextType, Register, RegisterType},
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
    /// The number of write commands.
    num_writes: u16,
}

impl<N: Network> Finalize<N> {
    /// Initializes a new finalize with the given name.
    pub fn new(name: Identifier<N>) -> Self {
        Self { name, inputs: IndexSet::new(), commands: Vec::new(), num_writes: 0 }
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
    pub fn commands(&self) -> &[Command<N>] {
        &self.commands
    }

    /// Returns the number of write commands.
    pub const fn num_writes(&self) -> u16 {
        self.num_writes
    }

    /// Returns the minimum number of microcredits required to run the finalize.
    pub fn cost_in_microcredits(&self) -> u64 {
        // Defines the cost of each command.
        let cost = |command: &Command<N>| match command {
            Command::Instruction(Instruction::Abs(_)) => 2_000,
            Command::Instruction(Instruction::AbsWrapped(_)) => 2_000,
            Command::Instruction(Instruction::Add(_)) => 2_000,
            Command::Instruction(Instruction::AddWrapped(_)) => 2_000,
            Command::Instruction(Instruction::And(_)) => 2_000,
            Command::Instruction(Instruction::AssertEq(_)) => 2_000,
            Command::Instruction(Instruction::AssertNeq(_)) => 2_000,
            Command::Instruction(Instruction::Call(_)) => 1_000_000_000_000, // Note: `call` is not allowed in a finalize.
            Command::Instruction(Instruction::Cast(_)) => 2_000,
            Command::Instruction(Instruction::CommitBHP256(_)) => 200_000,
            Command::Instruction(Instruction::CommitBHP512(_)) => 200_000,
            Command::Instruction(Instruction::CommitBHP768(_)) => 200_000,
            Command::Instruction(Instruction::CommitBHP1024(_)) => 200_000,
            Command::Instruction(Instruction::CommitPED64(_)) => 100_000,
            Command::Instruction(Instruction::CommitPED128(_)) => 100_000,
            Command::Instruction(Instruction::CommitToGroupBHP256(_)) => 200_000,
            Command::Instruction(Instruction::CommitToGroupBHP512(_)) => 200_000,
            Command::Instruction(Instruction::CommitToGroupBHP768(_)) => 200_000,
            Command::Instruction(Instruction::CommitToGroupBHP1024(_)) => 200_000,
            Command::Instruction(Instruction::CommitToGroupPED64(_)) => 100_000,
            Command::Instruction(Instruction::CommitToGroupPED128(_)) => 100_000,
            Command::Instruction(Instruction::Div(_)) => 10_000,
            Command::Instruction(Instruction::DivWrapped(_)) => 2_000,
            Command::Instruction(Instruction::Double(_)) => 2_000,
            Command::Instruction(Instruction::GreaterThan(_)) => 2_000,
            Command::Instruction(Instruction::GreaterThanOrEqual(_)) => 2_000,
            Command::Instruction(Instruction::HashBHP256(_)) => 200_000,
            Command::Instruction(Instruction::HashBHP512(_)) => 100_000,
            Command::Instruction(Instruction::HashBHP768(_)) => 100_000,
            Command::Instruction(Instruction::HashBHP1024(_)) => 100_000,
            Command::Instruction(Instruction::HashPED64(_)) => 20_000,
            Command::Instruction(Instruction::HashPED128(_)) => 30_000,
            Command::Instruction(Instruction::HashPSD2(_)) => 60_000,
            Command::Instruction(Instruction::HashPSD4(_)) => 100_000,
            Command::Instruction(Instruction::HashPSD8(_)) => 200_000,
            Command::Instruction(Instruction::HashManyPSD2(_)) => 1_000_000_000_000, // TODO (d0cd): Add when the opcode is supported.
            Command::Instruction(Instruction::HashManyPSD4(_)) => 1_000_000_000_000, // TODO (d0cd): Add when the opcode is supported.
            Command::Instruction(Instruction::HashManyPSD8(_)) => 1_000_000_000_000, // TODO (d0cd): Add when the opcode is supported.
            Command::Instruction(Instruction::HashToGroupBHP256(_)) => 200_000,
            Command::Instruction(Instruction::HashToGroupBHP512(_)) => 100_000,
            Command::Instruction(Instruction::HashToGroupBHP768(_)) => 100_000,
            Command::Instruction(Instruction::HashToGroupBHP1024(_)) => 100_000,
            Command::Instruction(Instruction::HashToGroupPED64(_)) => 10_000,
            Command::Instruction(Instruction::HashToGroupPED128(_)) => 20_000,
            Command::Instruction(Instruction::HashToGroupPSD2(_)) => 600_000,
            Command::Instruction(Instruction::HashToGroupPSD4(_)) => 700_000,
            Command::Instruction(Instruction::HashToGroupPSD8(_)) => 800_000,
            Command::Instruction(Instruction::HashToScalarPSD2(_)) => 60_000,
            Command::Instruction(Instruction::HashToScalarPSD4(_)) => 100_000,
            Command::Instruction(Instruction::HashToScalarPSD8(_)) => 200_000,
            Command::Instruction(Instruction::Inv(_)) => 10_000,
            Command::Instruction(Instruction::IsEq(_)) => 2_000,
            Command::Instruction(Instruction::IsNeq(_)) => 2_000,
            Command::Instruction(Instruction::LessThan(_)) => 2_000,
            Command::Instruction(Instruction::LessThanOrEqual(_)) => 2_000,
            Command::Instruction(Instruction::Modulo(_)) => 2_000,
            Command::Instruction(Instruction::Mul(_)) => 150_000,
            Command::Instruction(Instruction::MulWrapped(_)) => 2_000,
            Command::Instruction(Instruction::Nand(_)) => 2_000,
            Command::Instruction(Instruction::Neg(_)) => 2_000,
            Command::Instruction(Instruction::Nor(_)) => 2_000,
            Command::Instruction(Instruction::Not(_)) => 2_000,
            Command::Instruction(Instruction::Or(_)) => 2_000,
            Command::Instruction(Instruction::Pow(_)) => 20_000,
            Command::Instruction(Instruction::PowWrapped(_)) => 2_000,
            Command::Instruction(Instruction::Rem(_)) => 2_000,
            Command::Instruction(Instruction::RemWrapped(_)) => 2_000,
            Command::Instruction(Instruction::Shl(_)) => 2_000,
            Command::Instruction(Instruction::ShlWrapped(_)) => 2_000,
            Command::Instruction(Instruction::Shr(_)) => 2_000,
            Command::Instruction(Instruction::ShrWrapped(_)) => 2_000,
            Command::Instruction(Instruction::Square(_)) => 2_000,
            Command::Instruction(Instruction::SquareRoot(_)) => 120_000,
            Command::Instruction(Instruction::Sub(_)) => 10_000,
            Command::Instruction(Instruction::SubWrapped(_)) => 2_000,
            Command::Instruction(Instruction::Ternary(_)) => 2_000,
            Command::Instruction(Instruction::Xor(_)) => 2_000,
            Command::Get(_) => 1_000_000,
            Command::GetOrInit(_) => 1_000_000,
            Command::Set(_) => 1_000_000,
        };
        self.commands.iter().map(|command| cost(command)).sum()
    }
}

impl<N: Network> Finalize<N> {
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
    pub fn add_command(&mut self, command: Command<N>) -> Result<()> {
        // Ensure the maximum number of commands has not been exceeded.
        ensure!(self.commands.len() < N::MAX_COMMANDS, "Cannot add more than {} commands", N::MAX_COMMANDS);
        // Ensure the number of write commands has not been exceeded.
        ensure!(self.num_writes < N::MAX_WRITES, "Cannot add more than {} 'set' commands", N::MAX_WRITES);

        // Perform additional checks on the command.
        match &command {
            Command::Instruction(instruction) => {
                match instruction {
                    // Ensure the instruction is not a `call`.
                    Instruction::Call(_) => bail!("Forbidden operation: Finalize cannot invoke a 'call'"),
                    // Ensure the instruction is not a `cast` to a record.
                    Instruction::Cast(cast) if !matches!(cast.register_type(), &RegisterType::Plaintext(_)) => {
                        bail!("Forbidden operation: Finalize cannot cast to a record")
                    }
                    _ => {}
                }
                // Ensure the destination register is a locator.
                for register in instruction.destinations() {
                    ensure!(matches!(register, Register::Locator(..)), "Destination register must be a locator");
                }
            }
            Command::Get(get) => {
                // Ensure the destination register is a locator.
                ensure!(matches!(get.destination(), Register::Locator(..)), "Destination register must be a locator");
            }
            Command::GetOrUse(get_or_use) => {
                // Ensure the destination register is a locator.
                ensure!(
                    matches!(get_or_use.destination(), Register::Locator(..)),
                    "Destination register must be a locator"
                );
            }
            Command::Set(_) => {
                // Increment the number of write commands.
                self.num_writes += 1;
            }
        }

        // Insert the command.
        self.commands.push(command);
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
