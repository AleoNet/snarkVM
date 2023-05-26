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
    program::{Identifier, LiteralType, PlaintextType, Register, RegisterType},
};

use indexmap::{IndexMap, IndexSet};

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
    /// A mapping from labels defined in `Position` commands to their index in `commands`.
    label_indices: IndexMap<Identifier<N>, usize>,
}

impl<N: Network> Finalize<N> {
    /// Initializes a new finalize with the given name.
    pub fn new(name: Identifier<N>) -> Self {
        Self { name, inputs: IndexSet::new(), commands: Vec::new(), num_writes: 0, label_indices: IndexMap::new() }
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
    pub fn cost_in_microcredits(&self) -> Result<u64> {
        // Defines the cost of each command.
        let cost = |command: &Command<N>| match command {
            Command::Instruction(Instruction::Abs(_)) => Ok(2_000),
            Command::Instruction(Instruction::AbsWrapped(_)) => Ok(2_000),
            Command::Instruction(Instruction::Add(_)) => Ok(2_000),
            Command::Instruction(Instruction::AddWrapped(_)) => Ok(2_000),
            Command::Instruction(Instruction::And(_)) => Ok(2_000),
            Command::Instruction(Instruction::AssertEq(_)) => Ok(2_000),
            Command::Instruction(Instruction::AssertNeq(_)) => Ok(2_000),
            Command::Instruction(Instruction::Call(_)) => bail!("`call` is not supported in finalize."),
            Command::Instruction(Instruction::Cast(_)) => Ok(2_000),
            Command::Instruction(Instruction::CommitBHP256(_)) => Ok(200_000),
            Command::Instruction(Instruction::CommitBHP512(_)) => Ok(200_000),
            Command::Instruction(Instruction::CommitBHP768(_)) => Ok(200_000),
            Command::Instruction(Instruction::CommitBHP1024(_)) => Ok(200_000),
            Command::Instruction(Instruction::CommitPED64(_)) => Ok(100_000),
            Command::Instruction(Instruction::CommitPED128(_)) => Ok(100_000),
            Command::Instruction(Instruction::Div(_)) => Ok(10_000),
            Command::Instruction(Instruction::DivWrapped(_)) => Ok(2_000),
            Command::Instruction(Instruction::Double(_)) => Ok(2_000),
            Command::Instruction(Instruction::GreaterThan(_)) => Ok(2_000),
            Command::Instruction(Instruction::GreaterThanOrEqual(_)) => Ok(2_000),
            Command::Instruction(Instruction::HashBHP256(_)) => Ok(200_000),
            Command::Instruction(Instruction::HashBHP512(_)) => Ok(100_000),
            Command::Instruction(Instruction::HashBHP768(_)) => Ok(100_000),
            Command::Instruction(Instruction::HashBHP1024(_)) => Ok(100_000),
            Command::Instruction(Instruction::HashPED64(_)) => Ok(20_000),
            Command::Instruction(Instruction::HashPED128(_)) => Ok(30_000),
            Command::Instruction(Instruction::HashPSD2(hash)) => match hash.destination_type() {
                LiteralType::Address | LiteralType::Group => Ok(600_000),
                _ => Ok(60_000),
            },
            Command::Instruction(Instruction::HashPSD4(hash)) => match hash.destination_type() {
                LiteralType::Address | LiteralType::Group => Ok(700_000),
                _ => Ok(100_000),
            },
            Command::Instruction(Instruction::HashPSD8(hash)) => match hash.destination_type() {
                LiteralType::Address | LiteralType::Group => Ok(800_000),
                _ => Ok(200_000),
            },
            Command::Instruction(Instruction::HashManyPSD2(_)) => {
                bail!("`hash_many.psd2` is not supported in finalize.")
            }
            Command::Instruction(Instruction::HashManyPSD4(_)) => {
                bail!("`hash_many.psd4` is not supported in finalize.")
            }
            Command::Instruction(Instruction::HashManyPSD8(_)) => {
                bail!("`hash_many.psd8` is not supported in finalize.")
            }
            Command::Instruction(Instruction::Inv(_)) => Ok(10_000),
            Command::Instruction(Instruction::IsEq(_)) => Ok(2_000),
            Command::Instruction(Instruction::IsNeq(_)) => Ok(2_000),
            Command::Instruction(Instruction::LessThan(_)) => Ok(2_000),
            Command::Instruction(Instruction::LessThanOrEqual(_)) => Ok(2_000),
            Command::Instruction(Instruction::Modulo(_)) => Ok(2_000),
            Command::Instruction(Instruction::Mul(_)) => Ok(150_000),
            Command::Instruction(Instruction::MulWrapped(_)) => Ok(2_000),
            Command::Instruction(Instruction::Nand(_)) => Ok(2_000),
            Command::Instruction(Instruction::Neg(_)) => Ok(2_000),
            Command::Instruction(Instruction::Nor(_)) => Ok(2_000),
            Command::Instruction(Instruction::Not(_)) => Ok(2_000),
            Command::Instruction(Instruction::Or(_)) => Ok(2_000),
            Command::Instruction(Instruction::Pow(_)) => Ok(20_000),
            Command::Instruction(Instruction::PowWrapped(_)) => Ok(2_000),
            Command::Instruction(Instruction::Rem(_)) => Ok(2_000),
            Command::Instruction(Instruction::RemWrapped(_)) => Ok(2_000),
            Command::Instruction(Instruction::Shl(_)) => Ok(2_000),
            Command::Instruction(Instruction::ShlWrapped(_)) => Ok(2_000),
            Command::Instruction(Instruction::Shr(_)) => Ok(2_000),
            Command::Instruction(Instruction::ShrWrapped(_)) => Ok(2_000),
            Command::Instruction(Instruction::Square(_)) => Ok(2_000),
            Command::Instruction(Instruction::SquareRoot(_)) => Ok(120_000),
            Command::Instruction(Instruction::Sub(_)) => Ok(10_000),
            Command::Instruction(Instruction::SubWrapped(_)) => Ok(2_000),
            Command::Instruction(Instruction::Ternary(_)) => Ok(2_000),
            Command::Instruction(Instruction::Xor(_)) => Ok(2_000),
            // TODO: The following 'finalize' commands are currently priced higher than expected.
            //  Expect these numbers to change as their usage is stabilized.
            Command::Contains(_) => Ok(250_000),
            Command::Get(_) => Ok(500_000),
            Command::GetOrUse(_) => Ok(500_000),
            Command::RandChaCha(_) => Ok(500_000),
            Command::Remove(_) => Ok(10_000),
            Command::Set(_) => Ok(1_000_000),
            Command::Position(_) => Ok(1_000),
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
            Command::Contains(contains) => {
                // Ensure the destination register is a locator.
                ensure!(
                    matches!(contains.destination(), Register::Locator(..)),
                    "Destination register must be a locator"
                );
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
            Command::RandChaCha(rand_chacha) => {
                // Ensure the destination register is a locator.
                ensure!(
                    matches!(rand_chacha.destination(), Register::Locator(..)),
                    "Destination register must be a locator"
                );
            }
            Command::Remove(_) => {
                // Increment the number of write commands.
                self.num_writes += 1;
            }
            Command::Set(_) => {
                // Increment the number of write commands.
                self.num_writes += 1;
            }
            Command::Position(position) => {
                // Ensure that the label is not already defined.
                ensure!(
                    self.label_indices.get(position.label()).is_none(),
                    format!(" The label `{}` is not unique.", position.label())
                );
                // Add the label to mapping of labels to their index in `self.commands`.
                self.label_indices.insert(*position.label(), self.commands.len());
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
