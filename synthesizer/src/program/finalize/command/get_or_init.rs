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

use crate::{FinalizeOperation, FinalizeStorage, FinalizeStore, Load as LoadTrait, Opcode, Operand, Stack, Store};
use console::{
    network::prelude::*,
    program::{Identifier, Register, Value},
};

/// A get command that initializes the mapping in case of failure, e.g. `get.or_init accounts[r0] r1 into r2;`.
/// Gets the value stored at `operand` in `mapping` and stores the result in `destination`.
/// If the key is not present, `default` is stored in `mapping` and stored in `destination`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct GetOrInit<N: Network> {
    /// The mapping name.
    mapping: Identifier<N>,
    /// The key to access the mapping.
    key: Operand<N>,
    /// The default value.
    default: Operand<N>,
    /// The destination register.
    destination: Register<N>,
}

impl<N: Network> GetOrInit<N> {
    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        Opcode::Command("get.or_init")
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> Vec<Operand<N>> {
        vec![self.key.clone(), self.default.clone()]
    }

    /// Returns the mapping name.
    #[inline]
    pub const fn mapping_name(&self) -> &Identifier<N> {
        &self.mapping
    }

    /// Returns the operand containing the key.
    #[inline]
    pub const fn key(&self) -> &Operand<N> {
        &self.key
    }

    /// Returns the default value.
    #[inline]
    pub const fn default(&self) -> &Operand<N> {
        &self.default
    }

    /// Returns the destination register.
    #[inline]
    pub const fn destination(&self) -> &Register<N> {
        &self.destination
    }
}

impl<N: Network> GetOrInit<N> {
    /// Finalizes the command.
    #[inline]
    pub fn finalize<P: FinalizeStorage<N>>(
        &self,
        stack: &Stack<N>,
        store: &FinalizeStore<N, P>,
        registers: &mut (impl LoadTrait<N> + Store<N>),
    ) -> Result<Option<FinalizeOperation<N>>> {
        // Ensure the mapping exists in storage.
        if !store.contains_mapping_confirmed(stack.program_id(), &self.mapping)? {
            bail!("Mapping '{}/{}' does not exist in storage", stack.program_id(), self.mapping);
        }

        // Load the operand as a plaintext.
        let key = registers.load_plaintext(stack, &self.key)?;

        // Retrieve the value from storage as a literal.
        let (value, finalize_operation) = match store.get_value_speculative(stack.program_id(), &self.mapping, &key)? {
            Some(Value::Plaintext(plaintext)) => (Value::Plaintext(plaintext), None),
            Some(Value::Record(..)) => bail!("Cannot 'get.or_init' a 'record'"),
            // If a key does not exist, then store the default value into the mapping and return it.
            None => {
                // Store the default value into the mapping.
                let default = Value::Plaintext(registers.load_plaintext(stack, &self.default)?);
                // Return the default value and finalize operation.
                (default.clone(), Some(store.update_key_value(stack.program_id(), &self.mapping, key, default)?))
            }
        };

        // Assign the value to the destination register.
        registers.store(stack, &self.destination, value)?;

        // Return the finalize operation.
        Ok(finalize_operation)
    }
}

impl<N: Network> Parser for GetOrInit<N> {
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
        // Parse the key operand from the string.
        let (string, key) = Operand::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "]" from the string.
        let (string, _) = tag("]")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the default value from the string.
        let (string, default) = Operand::parse(string)?;

        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "into" keyword from the string.
        let (string, _) = tag("into")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the destination register from the string.
        let (string, destination) = Register::parse(string)?;

        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the ";" from the string.
        let (string, _) = tag(";")(string)?;

        Ok((string, Self { mapping, key, default, destination }))
    }
}

impl<N: Network> FromStr for GetOrInit<N> {
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

impl<N: Network> Debug for GetOrInit<N> {
    /// Prints the command as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for GetOrInit<N> {
    /// Prints the command to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Print the command.
        write!(f, "{} ", Self::opcode())?;
        // Print the mapping and key operand.
        write!(f, "{}[{}] {} into ", self.mapping, self.key, self.default)?;
        // Print the destination register.
        write!(f, "{};", self.destination)
    }
}

impl<N: Network> FromBytes for GetOrInit<N> {
    /// Reads the command from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the mapping name.
        let mapping = Identifier::read_le(&mut reader)?;
        // Read the key operand.
        let key = Operand::read_le(&mut reader)?;
        // Read the default value.
        let default = Operand::read_le(&mut reader)?;
        // Read the destination register.
        let destination = Register::read_le(&mut reader)?;
        // Return the command.
        Ok(Self { mapping, key, default, destination })
    }
}

impl<N: Network> ToBytes for GetOrInit<N> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the mapping name.
        self.mapping.write_le(&mut writer)?;
        // Write the key operand.
        self.key.write_le(&mut writer)?;
        // Write the default value.
        self.default.write_le(&mut writer)?;
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
        let (string, get_or_init) = GetOrInit::<CurrentNetwork>::parse("get.or_init account[r0] r1 into r2;").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(get_or_init.mapping, Identifier::from_str("account").unwrap());
        assert_eq!(get_or_init.operands().len(), 2, "The number of operands is incorrect");
        assert_eq!(get_or_init.key, Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(get_or_init.default, Operand::Register(Register::Locator(1)), "The second operand is incorrect");
        assert_eq!(get_or_init.destination, Register::Locator(2), "The second operand is incorrect");
    }
}
