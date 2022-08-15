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

mod decrement;
pub use decrement::*;

mod finalize;
pub use finalize::*;

mod increment;
pub use increment::*;

use crate::{program::Instruction, FinalizeRegisters, ProgramStorage, ProgramStore, Stack};
use console::network::prelude::*;

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Command<N: Network> {
    /// Decrements the value stored at the `first` operand in `mapping` by the amount in the `second` operand.
    Decrement(Decrement<N>),
    /// Evaluates the instruction.
    Instruction(Instruction<N>),
    /// Increments the value stored at the `first` operand in `mapping` by the amount in the `second` operand.
    Increment(Increment<N>),
}

impl<N: Network> Command<N> {
    /// Evaluates the command.
    #[inline]
    pub fn evaluate_finalize<P: ProgramStorage<N>>(
        &self,
        stack: &Stack<N>,
        store: &ProgramStore<N, P>,
        registers: &mut FinalizeRegisters<N>,
    ) -> Result<()> {
        match self {
            Command::Decrement(decrement) => decrement.evaluate_finalize(stack, store, registers),
            // TODO (howardwu): Implement support for instructions (consider using a trait for `Registers::load/store`).
            // Command::Instruction(instruction) => instruction.evaluate_finalize(stack, registers),
            Command::Instruction(_) => bail!("Instructions in 'finalize' are not supported (yet)."),
            Command::Increment(increment) => increment.evaluate_finalize(stack, store, registers),
        }
    }
}

impl<N: Network> FromBytes for Command<N> {
    /// Reads the command from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the variant.
        let variant = u8::read_le(&mut reader)?;
        match variant {
            // Read the decrement.
            0 => Ok(Self::Decrement(Decrement::read_le(&mut reader)?)),
            // Read the instruction.
            1 => Ok(Self::Instruction(Instruction::read_le(&mut reader)?)),
            // Read the increment.
            2 => Ok(Self::Increment(Increment::read_le(&mut reader)?)),
            // Invalid variant.
            3.. => Err(error(format!("Invalid command variant: {}", variant))),
        }
    }
}

impl<N: Network> ToBytes for Command<N> {
    /// Writes the command to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::Decrement(decrement) => {
                // Write the variant.
                0u8.write_le(&mut writer)?;
                // Write the decrement.
                decrement.write_le(&mut writer)
            }
            Self::Instruction(instruction) => {
                // Write the variant.
                1u8.write_le(&mut writer)?;
                // Write the instruction.
                instruction.write_le(&mut writer)
            }
            Self::Increment(increment) => {
                // Write the variant.
                2u8.write_le(&mut writer)?;
                // Write the increment.
                increment.write_le(&mut writer)
            }
        }
    }
}

impl<N: Network> Parser for Command<N> {
    /// Parses the string into the command.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        alt((
            map(Decrement::parse, |decrement| Self::Decrement(decrement)),
            map(Instruction::parse, |instruction| Self::Instruction(instruction)),
            map(Increment::parse, |increment| Self::Increment(increment)),
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
            Self::Decrement(decrement) => Display::fmt(decrement, f),
            Self::Instruction(instruction) => Display::fmt(instruction, f),
            Self::Increment(increment) => Display::fmt(increment, f),
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
        let command = Command::<CurrentNetwork>::parse(expected).unwrap().1;
        let bytes = command.to_bytes_le().unwrap();
        assert_eq!(command, Command::from_bytes_le(&bytes).unwrap());

        // Instruction
        let expected = "add r0 r1 into r2;";
        let command = Command::<CurrentNetwork>::parse(expected).unwrap().1;
        let bytes = command.to_bytes_le().unwrap();
        assert_eq!(command, Command::from_bytes_le(&bytes).unwrap());

        // Increment
        let expected = "increment object[r0] by r1;";
        let command = Command::<CurrentNetwork>::parse(expected).unwrap().1;
        let bytes = command.to_bytes_le().unwrap();
        assert_eq!(command, Command::from_bytes_le(&bytes).unwrap());
    }

    #[test]
    fn test_command_parse() {
        // Decrement
        let expected = "decrement object[r0] by r1;";
        let command = Command::<CurrentNetwork>::parse(expected).unwrap().1;
        assert_eq!(Command::Decrement(Decrement::from_str(expected).unwrap()), command);
        assert_eq!(expected, command.to_string());

        // Instruction
        let expected = "add r0 r1 into r2;";
        let command = Command::<CurrentNetwork>::parse(expected).unwrap().1;
        assert_eq!(Command::Instruction(Instruction::from_str(expected).unwrap()), command);
        assert_eq!(expected, command.to_string());

        // Increment
        let expected = "increment object[r0] by r1;";
        let command = Command::<CurrentNetwork>::parse(expected).unwrap().1;
        assert_eq!(Command::Increment(Increment::from_str(expected).unwrap()), command);
        assert_eq!(expected, command.to_string());
    }
}
