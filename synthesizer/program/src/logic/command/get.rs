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

use crate::{
    traits::{FinalizeStoreTrait, RegistersLoad, RegistersStore, StackMatches, StackProgram},
    Opcode,
    Operand,
};
use console::{
    network::prelude::*,
    program::{Identifier, Locator, Register, Value},
};

use std::io::{BufRead, BufReader};

/// The operator references a local or external mapping name.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum MappingLocator<N: Network> {
    /// The reference to a non-local mapping name.
    Locator(Locator<N>),
    /// The reference to a local mapping name.
    Resource(Identifier<N>),
}

impl<N: Network> Parser for MappingLocator<N> {
    /// Parses a string into an operator.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        alt((
            map(Locator::parse, |locator| MappingLocator::Locator(locator)),
            map(Identifier::parse, |identifier| MappingLocator::Resource(identifier)),
        ))(string)
    }
}

impl<N: Network> FromStr for MappingLocator<N> {
    type Err = Error;

    /// Parses a string into an operator.
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

impl<N: Network> Debug for MappingLocator<N> {
    /// Prints the operator as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for MappingLocator<N> {
    /// Prints the operator to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            MappingLocator::Locator(locator) => Display::fmt(locator, f),
            MappingLocator::Resource(resource) => Display::fmt(resource, f),
        }
    }
}

impl<N: Network> FromBytes for MappingLocator<N> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the version.
        let version = u8::read_le(&mut reader)?;
        // Ensure the version is valid.
        if version != 0 {
            return Err(error("Failed to read MappingLocator. Invalid version."));
        }
        // Read the variant.
        let variant = u8::read_le(&mut reader)?;
        // Match the variant.
        match variant {
            0 => Ok(MappingLocator::Locator(Locator::read_le(&mut reader)?)),
            1 => Ok(MappingLocator::Resource(Identifier::read_le(&mut reader)?)),
            _ => Err(error("Failed to read MappingLocator. Invalid variant.")),
        }
    }
}

impl<N: Network> ToBytes for MappingLocator<N> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            MappingLocator::Locator(locator) => {
                // Write the version.
                0u8.write_le(&mut writer)?;
                // Write the variant.
                0u8.write_le(&mut writer)?;
                // Write the locator.
                locator.write_le(&mut writer)
            }
            MappingLocator::Resource(resource) => {
                // Write the version.
                0u8.write_le(&mut writer)?;
                // Write the variant.
                1u8.write_le(&mut writer)?;
                // Write the resource.
                resource.write_le(&mut writer)
            }
        }
    }
}

/// A get command, e.g. `get accounts[r0] into r1;`.
/// Gets the value stored at `operand` in `mapping` and stores the result in `destination`.
#[derive(Clone)]
pub struct Get<N: Network> {
    /// The mapping.
    // TODO (howardwu): For mainnet - Use `CallOperator`, delete the above `MappingLocator`.
    mapping: MappingLocator<N>,
    /// The key to access the mapping.
    key: Operand<N>,
    /// The destination register.
    destination: Register<N>,
}

impl<N: Network> PartialEq for Get<N> {
    /// Returns true if the two objects are equal.
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.mapping == other.mapping && self.key == other.key && self.destination == other.destination
    }
}

impl<N: Network> Eq for Get<N> {}

impl<N: Network> std::hash::Hash for Get<N> {
    /// Returns the hash of the object.
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.mapping.hash(state);
        self.key.hash(state);
        self.destination.hash(state);
    }
}

impl<N: Network> Get<N> {
    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        Opcode::Command("get")
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> Vec<Operand<N>> {
        vec![self.key.clone()]
    }

    /// Returns the mapping.
    #[inline]
    pub const fn mapping(&self) -> &MappingLocator<N> {
        &self.mapping
    }

    /// Returns the operand containing the key.
    #[inline]
    pub const fn key(&self) -> &Operand<N> {
        &self.key
    }

    /// Returns the destination register.
    #[inline]
    pub const fn destination(&self) -> &Register<N> {
        &self.destination
    }
}

impl<N: Network> Get<N> {
    /// Finalizes the command.
    #[inline]
    pub fn finalize(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        store: &impl FinalizeStoreTrait<N>,
        registers: &mut (impl RegistersLoad<N> + RegistersStore<N>),
    ) -> Result<()> {
        // Determine the program ID and mapping name.
        let (program_id, mapping_name) = match self.mapping {
            MappingLocator::Locator(locator) => (*locator.program_id(), *locator.resource()),
            MappingLocator::Resource(mapping_name) => (*stack.program_id(), mapping_name),
        };

        // Ensure the mapping exists in storage.
        if !store.contains_mapping_confirmed(&program_id, &mapping_name)? {
            bail!("Mapping '{program_id}/{mapping_name}' does not exist in storage");
        }

        // Load the operand as a plaintext.
        let key = registers.load_plaintext(stack, &self.key)?;

        // Retrieve the value from storage as a literal.
        let value = match store.get_value_speculative(program_id, mapping_name, &key)? {
            Some(Value::Plaintext(plaintext)) => Value::Plaintext(plaintext),
            Some(Value::Record(..)) => bail!("Cannot 'get' a 'record'"),
            Some(Value::Future(..)) => bail!("Cannot 'get' a 'future'",),
            // If a key does not exist, then bail.
            None => bail!("Key '{key}' does not exist in mapping '{program_id}/{mapping_name}'"),
        };

        // Assign the value to the destination register.
        registers.store(stack, &self.destination, value)?;

        Ok(())
    }
}

impl<N: Network> Parser for Get<N> {
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
        let (string, mapping) = MappingLocator::parse(string)?;
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

        Ok((string, Self { mapping, key, destination }))
    }
}

impl<N: Network> FromStr for Get<N> {
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

impl<N: Network> Debug for Get<N> {
    /// Prints the command as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Get<N> {
    /// Prints the command to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Print the command.
        write!(f, "{} ", Self::opcode())?;
        // Print the mapping and key operand.
        write!(f, "{}[{}] into ", self.mapping, self.key)?;
        // Print the destination register.
        write!(f, "{};", self.destination)
    }
}

impl<N: Network> FromBytes for Get<N> {
    /// Reads the command from a buffer.
    fn read_le<R: Read>(reader: R) -> IoResult<Self> {
        // Peek at the first byte.
        // TODO (howardwu): For mainnet - Read a `MappingLocator`.
        let mut reader = BufReader::with_capacity(1, reader);
        let first_byte = {
            let buffer = reader.fill_buf()?;
            match buffer.first() {
                Some(byte) => *byte,
                None => return Err(error("Failed to read `get`. Expected byte.")),
            }
        };
        // If the first byte is zero, then read a `MappingLocator`, otherwise read an `Identifier`.
        let mapping = match first_byte {
            0u8 => MappingLocator::read_le(&mut reader)?,
            _ => MappingLocator::Resource(Identifier::read_le(&mut reader)?),
        };
        // Read the key operand.
        let key = Operand::read_le(&mut reader)?;
        // Read the destination register.
        let destination = Register::read_le(&mut reader)?;
        // Return the command.
        Ok(Self { mapping, key, destination })
    }
}

impl<N: Network> ToBytes for Get<N> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the mapping name.
        // TODO (howardwu): For mainnet - Write `self.mapping` directly, instead of matching on the identifier case.
        match &self.mapping {
            MappingLocator::Locator(_) => self.mapping.write_le(&mut writer)?,
            MappingLocator::Resource(identifier) => identifier.write_le(&mut writer)?,
        }
        // Write the key operand.
        self.key.write_le(&mut writer)?;
        // Write the destination register.
        self.destination.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::{network::Testnet3, program::Register};

    type CurrentNetwork = Testnet3;

    struct OldGet<N: Network> {
        mapping: Identifier<N>,
        key: Operand<N>,
        destination: Register<N>,
    }

    impl<N: Network> ToBytes for OldGet<N> {
        fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()>
        where
            Self: Sized,
        {
            // Write the mapping name.
            self.mapping.write_le(&mut writer)?;
            // Write the key operand.
            self.key.write_le(&mut writer)?;
            // Write the destination register.
            self.destination.write_le(&mut writer)
        }
    }

    #[test]
    fn test_parse() {
        let (string, get) = Get::<CurrentNetwork>::parse("get account[r0] into r1;").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(get.mapping, MappingLocator::from_str("account").unwrap());
        assert_eq!(get.operands().len(), 1, "The number of operands is incorrect");
        assert_eq!(get.key, Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(get.destination, Register::Locator(1), "The second operand is incorrect");

        let (string, get) = Get::<CurrentNetwork>::parse("get token.aleo/balances[r0] into r1;").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(get.mapping, MappingLocator::from_str("token.aleo/balances").unwrap());
        assert_eq!(get.operands().len(), 1, "The number of operands is incorrect");
        assert_eq!(get.key, Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(get.destination, Register::Locator(1), "The second operand is incorrect");
    }

    #[test]
    fn test_from_bytes() {
        let (string, get) = Get::<CurrentNetwork>::parse("get account[r0] into r1;").unwrap();
        assert!(string.is_empty());

        let old_get = OldGet::<CurrentNetwork> {
            mapping: Identifier::from_str("account").unwrap(),
            key: Operand::Register(Register::Locator(0)),
            destination: Register::Locator(1),
        };

        let get_bytes = get.to_bytes_le().unwrap();
        let old_get_bytes = old_get.to_bytes_le().unwrap();

        let first = Get::<CurrentNetwork>::from_bytes_le(&get_bytes[..]).unwrap();
        let second = Get::<CurrentNetwork>::from_bytes_le(&old_get_bytes[..]).unwrap();
        assert_eq!(first, second);
    }
}
