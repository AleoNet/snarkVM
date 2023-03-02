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

use crate::{Opcode, Operand};
use console::{
    network::prelude::*,
    program::{Identifier, Literal, Plaintext, Value},
};

/// Increments the value stored at the `first` operand in `mapping` by the amount in the `second` operand.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Increment<N: Network> {
    /// The mapping name.
    mapping: Identifier<N>,
    /// The first operand.
    first: Operand<N>,
    /// The second operand.
    second: Operand<N>,
}

impl<N: Network> Increment<N> {
    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        Opcode::Command("increment")
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> Vec<Operand<N>> {
        vec![self.first.clone(), self.second.clone()]
    }

    /// Returns the mapping name.
    #[inline]
    pub const fn mapping_name(&self) -> &Identifier<N> {
        &self.mapping
    }

    /// Returns the operand containing the key.
    #[inline]
    pub const fn key(&self) -> &Operand<N> {
        &self.first
    }

    /// Returns the operand containing the value.
    #[inline]
    pub const fn value(&self) -> &Operand<N> {
        &self.second
    }
}

impl<N: Network> Parser for Increment<N> {
    /// Parses a string into an operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the opcode from the string.
        let (string, _) = tag(*Self::opcode())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;

        // Parse the mapping name from the string.
        let (string, mapping) = Identifier::parse(string)?;
        // Parse the "[" from the string.
        let (string, _) = tag("[")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the first operand from the string.
        let (string, first) = Operand::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "]" from the string.
        let (string, _) = tag("]")(string)?;

        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "by" from the string.
        let (string, _) = tag("by")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the second operand from the string.
        let (string, second) = Operand::parse(string)?;

        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the ";" from the string.
        let (string, _) = tag(";")(string)?;

        Ok((string, Self { mapping, first, second }))
    }
}

impl<N: Network> FromStr for Increment<N> {
    type Err = Error;

    /// Parses a string into the command.
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

impl<N: Network> Debug for Increment<N> {
    /// Prints the command as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Increment<N> {
    /// Prints the command to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Print the command.
        write!(f, "{} ", Self::opcode())?;
        // Print the first operand.
        write!(f, "{}[{}] ", self.mapping, self.first)?;
        // Print the "by" operand.
        write!(f, "by ")?;
        // Print the second operand.
        write!(f, "{};", self.second)
    }
}

impl<N: Network> FromBytes for Increment<N> {
    /// Reads the command from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the mapping name.
        let mapping = Identifier::read_le(&mut reader)?;
        // Read the first operand.
        let first = Operand::read_le(&mut reader)?;
        // Read the second operand.
        let second = Operand::read_le(&mut reader)?;
        // Return the command.
        Ok(Self { mapping, first, second })
    }
}

impl<N: Network> ToBytes for Increment<N> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the mapping name.
        self.mapping.write_le(&mut writer)?;
        // Write the first operand.
        self.first.write_le(&mut writer)?;
        // Write the second operand.
        self.second.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::{network::Testnet3, program::Register};

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_parse() {
        let (string, increment) = Increment::<CurrentNetwork>::parse("increment account[r0] by r1;").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(increment.mapping, Identifier::from_str("account").unwrap());
        assert_eq!(increment.operands().len(), 2, "The number of operands is incorrect");
        assert_eq!(increment.first, Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(increment.second, Operand::Register(Register::Locator(1)), "The second operand is incorrect");
    }
}
