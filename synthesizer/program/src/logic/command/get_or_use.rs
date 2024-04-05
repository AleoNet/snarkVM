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
    CallOperator,
    Opcode,
    Operand,
};
use console::{
    network::prelude::*,
    program::{Register, Value},
};

/// A get command that uses the provided default in case of failure, e.g. `get.or_use accounts[r0] r1 into r2;`.
/// Gets the value stored at `operand` in `mapping` and stores the result in `destination`.
/// If the key is not present, `default` is stored in `destination`.
#[derive(Clone)]
pub struct GetOrUse<N: Network> {
    /// The mapping.
    mapping: CallOperator<N>,
    /// The key to access the mapping.
    key: Operand<N>,
    /// The default value.
    default: Operand<N>,
    /// The destination register.
    destination: Register<N>,
}

impl<N: Network> PartialEq for GetOrUse<N> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.mapping == other.mapping
            && self.key == other.key
            && self.default == other.default
            && self.destination == other.destination
    }
}

impl<N: Network> Eq for GetOrUse<N> {}

impl<N: Network> std::hash::Hash for GetOrUse<N> {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.mapping.hash(state);
        self.key.hash(state);
        self.default.hash(state);
        self.destination.hash(state);
    }
}

impl<N: Network> GetOrUse<N> {
    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        Opcode::Command("get.or_use")
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> Vec<Operand<N>> {
        vec![self.key.clone(), self.default.clone()]
    }

    /// Returns the mapping.
    #[inline]
    pub const fn mapping(&self) -> &CallOperator<N> {
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

impl<N: Network> GetOrUse<N> {
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
            CallOperator::Locator(locator) => (*locator.program_id(), *locator.resource()),
            CallOperator::Resource(mapping_name) => (*stack.program_id(), mapping_name),
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
            Some(Value::Record(..)) => bail!("Cannot 'get.or_use' a 'record'"),
            Some(Value::Future(..)) => bail!("Cannot 'get.or_use' a 'future'"),
            // If a key does not exist, then use the default value.
            None => Value::Plaintext(registers.load_plaintext(stack, &self.default)?),
        };

        // Assign the value to the destination register.
        registers.store(stack, &self.destination, value)?;

        // Return the finalize operation.
        Ok(())
    }
}

impl<N: Network> Parser for GetOrUse<N> {
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
        let (string, mapping) = CallOperator::parse(string)?;
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

impl<N: Network> FromStr for GetOrUse<N> {
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

impl<N: Network> Debug for GetOrUse<N> {
    /// Prints the command as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for GetOrUse<N> {
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

impl<N: Network> FromBytes for GetOrUse<N> {
    /// Reads the command from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the mapping name.
        let mapping = CallOperator::read_le(&mut reader)?;
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

impl<N: Network> ToBytes for GetOrUse<N> {
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
    use console::{network::MainnetV0, program::Register};

    type CurrentNetwork = MainnetV0;

    #[test]
    fn test_parse() {
        let (string, get_or_use) = GetOrUse::<CurrentNetwork>::parse("get.or_use account[r0] r1 into r2;").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(get_or_use.mapping, CallOperator::from_str("account").unwrap());
        assert_eq!(get_or_use.operands().len(), 2, "The number of operands is incorrect");
        assert_eq!(get_or_use.key, Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(get_or_use.default, Operand::Register(Register::Locator(1)), "The second operand is incorrect");
        assert_eq!(get_or_use.destination, Register::Locator(2), "The second operand is incorrect");

        let (string, get_or_use) =
            GetOrUse::<CurrentNetwork>::parse("get.or_use token.aleo/balances[r0] r1 into r2;").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(get_or_use.mapping, CallOperator::from_str("token.aleo/balances").unwrap());
        assert_eq!(get_or_use.operands().len(), 2, "The number of operands is incorrect");
        assert_eq!(get_or_use.key, Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(get_or_use.default, Operand::Register(Register::Locator(1)), "The second operand is incorrect");
        assert_eq!(get_or_use.destination, Register::Locator(2), "The second operand is incorrect");
    }

    #[test]
    fn test_from_bytes() {
        let (string, get_or_use) = GetOrUse::<CurrentNetwork>::parse("get.or_use account[r0] r1 into r2;").unwrap();
        assert!(string.is_empty());
        let bytes_le = get_or_use.to_bytes_le().unwrap();
        let result = GetOrUse::<CurrentNetwork>::from_bytes_le(&bytes_le[..]);
        assert!(result.is_ok());
    }
}
