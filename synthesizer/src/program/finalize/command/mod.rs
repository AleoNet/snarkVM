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

mod finalize;
pub use finalize::*;

mod load;
pub use load::*;

mod load_or;
pub use load_or::*;

mod store;
pub use store::*;

use crate::{program::Instruction, FinalizeRegisters, ProgramStorage, ProgramStore, Speculate, Stack};
use console::network::prelude::*;

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Command<N: Network> {
    /// Evaluates the instruction.
    Instruction(Instruction<N>),
    /// Loads the value stored at the `key` operand in `mapping` into `destination`.
    Load(Load<N>),
    /// Loads the value stored at the `key` operand in `mapping` into `destination`, using `default` if the key is not present.
    LoadDefault(LoadOr<N>),
    /// Stores the `value` operand into the `key` entry in `mapping`.
    Store(Store<N>),
}

impl<N: Network> Command<N> {
    /// Evaluates the command.
    #[inline]
    pub fn evaluate_finalize<P: ProgramStorage<N>>(
        &self,
        stack: &Stack<N>,
        program_store: &ProgramStore<N, P>,
        registers: &mut FinalizeRegisters<N>,
    ) -> Result<()> {
        match self {
            Command::Instruction(instruction) => instruction.evaluate_finalize(stack, registers),
            Command::Load(load) => load.evaluate_finalize(stack, program_store, registers),
            Command::LoadDefault(load_or) => load_or.evaluate_finalize(stack, program_store, registers),
            Command::Store(store) => store.evaluate_finalize(stack, program_store, registers),
        }
    }

    /// Speculatively evaluate the command.
    #[inline]
    pub fn speculate_finalize<P: ProgramStorage<N>>(
        &self,
        stack: &Stack<N>,
        program_store: &ProgramStore<N, P>,
        registers: &mut FinalizeRegisters<N>,
        speculate: &mut Speculate<N>,
    ) -> Result<()> {
        match self {
            Command::Instruction(instruction) => instruction.evaluate_finalize(stack, registers),
            Command::Load(load) => load.speculate_finalize(stack, program_store, registers, speculate),
            Command::LoadDefault(load_or) => load_or.speculate_finalize(stack, program_store, registers, speculate),
            Command::Store(store) => store.speculate_finalize(stack, program_store, registers, speculate),
        }
    }
}

impl<N: Network> FromBytes for Command<N> {
    /// Reads the command from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the variant.
        let variant = u8::read_le(&mut reader)?;
        match variant {
            // Read the instruction.
            0 => Ok(Self::Instruction(Instruction::read_le(&mut reader)?)),
            // Read the load.
            1 => Ok(Self::Load(Load::read_le(&mut reader)?)),
            // Read the default load.
            2 => Ok(Self::LoadDefault(LoadOr::read_le(&mut reader)?)),
            // Read the store.
            3 => Ok(Self::Store(Store::read_le(&mut reader)?)),
            // Invalid variant.
            4.. => Err(error(format!("Invalid command variant: {variant}"))),
        }
    }
}

impl<N: Network> ToBytes for Command<N> {
    /// Writes the command to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::Instruction(instruction) => {
                // Write the variant.
                0u8.write_le(&mut writer)?;
                // Write the instruction.
                instruction.write_le(&mut writer)
            }
            Self::Load(load) => {
                // Write the variant.
                1u8.write_le(&mut writer)?;
                // Write the load.
                load.write_le(&mut writer)
            }
            Self::LoadDefault(load_or) => {
                // Write the variant.
                2u8.write_le(&mut writer)?;
                // Write the defaulting load.
                load_or.write_le(&mut writer)
            }
            Self::Store(store) => {
                // Write the variant.
                3u8.write_le(&mut writer)?;
                // Write the store.
                store.write_le(&mut writer)
            }
        }
    }
}

impl<N: Network> Parser for Command<N> {
    /// Parses the string into the command.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the command.
        // Note that the order of the parsers is important.
        alt((
            map(LoadOr::parse, |load_or| Self::LoadDefault(load_or)),
            map(Load::parse, |load| Self::Load(load)),
            map(Store::parse, |store| Self::Store(store)),
            map(Instruction::parse, |instruction| Self::Instruction(instruction)),
        ))(string)
    }
}

impl<N: Network> FromStr for Command<N> {
    type Err = Error;

    /// Parses the string into the command.
    #[inline]
    fn from_str(string: &str) -> Result<Self> {
        match Self::parse(string) {
            Ok((remainder, object)) => {
                // Ensure the remainder is empty.
                ensure!(remainder.is_empty(), "Failed to parse string. Found invalid character in: \"{remainder}\"");
                // Return the object.
                Ok(object)
            }
            Err(error) => bail!("Failed to parse string. {error}"),
        }
    }
}

impl<N: Network> Debug for Command<N> {
    /// Prints the command as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Command<N> {
    /// Prints the command as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Instruction(instruction) => Display::fmt(instruction, f),
            Self::Load(load) => Display::fmt(load, f),
            Self::LoadDefault(load_or) => Display::fmt(load_or, f),
            Self::Store(store) => Display::fmt(store, f),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_command_bytes() {
        // Decrement
        let expected = "decrement object[r0] by r1;";
        Command::<CurrentNetwork>::parse(expected).unwrap_err();

        // Instruction
        let expected = "add r0 r1 into r2;";
        let command = Command::<CurrentNetwork>::parse(expected).unwrap().1;
        let bytes = command.to_bytes_le().unwrap();
        assert_eq!(command, Command::from_bytes_le(&bytes).unwrap());

        // Increment
        let expected = "increment object[r0] by r1;";
        Command::<CurrentNetwork>::parse(expected).unwrap_err();

        // Load
        let expected = "load object[r0] into r1;";
        let command = Command::<CurrentNetwork>::parse(expected).unwrap().1;
        let bytes = command.to_bytes_le().unwrap();
        assert_eq!(command, Command::from_bytes_le(&bytes).unwrap());

        // Load default
        let expected = "load_or object[r0] r1 into r2;";
        let command = Command::<CurrentNetwork>::parse(expected).unwrap().1;
        let bytes = command.to_bytes_le().unwrap();
        assert_eq!(command, Command::from_bytes_le(&bytes).unwrap());

        // Store
        let expected = "store r0 into object[r1];";
        let command = Command::<CurrentNetwork>::parse(expected).unwrap().1;
        let bytes = command.to_bytes_le().unwrap();
        assert_eq!(command, Command::from_bytes_le(&bytes).unwrap());
    }

    #[test]
    fn test_command_parse() {
        // Decrement
        let expected = "decrement object[r0] by r1;";
        Command::<CurrentNetwork>::parse(expected).unwrap_err();

        // Instruction
        let expected = "add r0 r1 into r2;";
        let command = Command::<CurrentNetwork>::parse(expected).unwrap().1;
        assert_eq!(Command::Instruction(Instruction::from_str(expected).unwrap()), command);
        assert_eq!(expected, command.to_string());

        // Increment
        let expected = "increment object[r0] by r1;";
        Command::<CurrentNetwork>::parse(expected).unwrap_err();

        // Load
        let expected = "load object[r0] into r1;";
        let command = Command::<CurrentNetwork>::parse(expected).unwrap().1;
        assert_eq!(Command::Load(Load::from_str(expected).unwrap()), command);
        assert_eq!(expected, command.to_string());

        // Load default
        let expected = "load_or object[r0] r1 into r2;";
        let command = Command::<CurrentNetwork>::parse(expected).unwrap().1;
        assert_eq!(Command::LoadDefault(LoadOr::from_str(expected).unwrap()), command);
        assert_eq!(expected, command.to_string());

        // Store
        let expected = "store r0 into object[r1];";
        let command = Command::<CurrentNetwork>::parse(expected).unwrap().1;
        assert_eq!(Command::Store(Store::from_str(expected).unwrap()), command);
        assert_eq!(expected, command.to_string());
    }
}
