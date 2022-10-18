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

use crate::{FinalizeRegisters, Opcode, Operand, ProgramStorage, ProgramStore, Stack};
use console::{
    network::prelude::*,
    program::{Identifier, Register, Value},
};

/// Loads the value stored at `operand` in `mapping` into `destination`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Load<N: Network> {
    /// The mapping name.
    mapping: Identifier<N>,
    /// The key to access the mapping.
    operand: Operand<N>,
    /// The destination register.
    destination: Register<N>,
}

impl<N: Network> Load<N> {
    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        Opcode::Command("load")
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> Vec<Operand<N>> {
        vec![self.operand.clone()]
    }

    /// Returns the mapping name.
    #[inline]
    pub const fn mapping_name(&self) -> &Identifier<N> {
        &self.mapping
    }

    /// Returns the operand containing the key.
    #[inline]
    pub const fn key(&self) -> &Operand<N> {
        &self.operand
    }

    /// Returns the destination register.
    #[inline]
    pub const fn destination(&self) -> &Register<N> {
        &self.destination
    }
}

impl<N: Network> Load<N> {
    /// Evaluates the command.
    #[inline]
    pub fn evaluate_finalize<P: ProgramStorage<N>>(
        &self,
        stack: &Stack<N>,
        store: &ProgramStore<N, P>,
        registers: &mut FinalizeRegisters<N>,
    ) -> Result<()> {
        // Ensure the mapping exists in storage.
        if !store.contains_mapping(stack.program_id(), &self.mapping)? {
            bail!("Mapping '{}/{}' does not exist in storage", stack.program_id(), self.mapping);
        }

        // Load the operand as a plaintext.
        let operand = registers.load_plaintext(stack, &self.operand)?;

        // Retrieve the value from storage as a literal.
        let value = match store.get_value(stack.program_id(), &self.mapping, &operand)? {
            Some(Value::Plaintext(plaintext)) => Value::Plaintext(plaintext),
            Some(Value::Record(..)) => bail!("Cannot 'load' a 'record'"),
            // If the key does not exist, use a default value.
            // TODO: Infer type.
            None => todo!(),
        };

        // Assign the value to the destination register.
        registers.store(stack, &self.destination, value)?;

        Ok(())
    }
}

impl<N: Network> Parser for Load<N> {
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
        let (string, operand) = Operand::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "]" from the string.
        let (string, _) = tag("]")(string)?;

        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "by" from the string.
        let (string, _) = tag("into")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the second operand from the string.
        let (string, destination) = Register::parse(string)?;

        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the ";" from the string.
        let (string, _) = tag(";")(string)?;

        Ok((string, Self { mapping, operand, destination }))
    }
}

impl<N: Network> FromStr for Load<N> {
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

impl<N: Network> Debug for Load<N> {
    /// Prints the command as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Load<N> {
    /// Prints the command to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Print the command.
        write!(f, "{} ", Self::opcode())?;
        // Print the mapping and operand.
        write!(f, "{}[{}] ", self.mapping, self.operand)?;
        // Print the "into " keyword.
        write!(f, "into ")?;
        // Print the destination register.
        write!(f, "{};", self.destination)
    }
}

impl<N: Network> FromBytes for Load<N> {
    /// Reads the command from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the mapping name.
        let mapping = Identifier::read_le(&mut reader)?;
        // Read the operand.
        let operand = Operand::read_le(&mut reader)?;
        // Read the destination register.
        let destination = Register::read_le(&mut reader)?;
        // Return the command.
        Ok(Self { mapping, operand, destination })
    }
}

impl<N: Network> ToBytes for Load<N> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the mapping name.
        self.mapping.write_le(&mut writer)?;
        // Write the operand.
        self.operand.write_le(&mut writer)?;
        // Write the destination register.
        self.destination.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::{network::Testnet3, program::Register};

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_parse() {
        let (string, load) = Load::<CurrentNetwork>::parse("load account[r0] into r1;").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(load.mapping, Identifier::from_str("account").unwrap());
        assert_eq!(load.operands().len(), 1, "The number of operands is incorrect");
        assert_eq!(load.operand, Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(load.destination, Register::Locator(1), "The second operand is incorrect");
    }
}
