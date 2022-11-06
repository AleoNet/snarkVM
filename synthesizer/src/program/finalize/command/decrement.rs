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
    program::{Identifier, Literal, Plaintext, Value},
};

/// Decrements the value stored at the `first` operand in `mapping` by the amount in the `second` operand.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Decrement<N: Network> {
    /// The mapping name.
    mapping: Identifier<N>,
    /// The first operand.
    first: Operand<N>,
    /// The second operand.
    second: Operand<N>,
}

impl<N: Network> Decrement<N> {
    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        Opcode::Command("decrement")
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

impl<N: Network> Decrement<N> {
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

        // Load the first operand as a plaintext.
        let key = registers.load_plaintext(stack, &self.first)?;
        // Load the second operand as a literal.
        let decrement = registers.load_literal(stack, &self.second)?;

        // Retrieve the starting value from storage as a literal.
        let start = match store.get_value(stack.program_id(), &self.mapping, &key)? {
            Some(Value::Plaintext(Plaintext::Literal(literal, _))) => literal,
            Some(Value::Plaintext(Plaintext::Struct(..))) => bail!("Cannot 'decrement' by an 'struct'"),
            Some(Value::Record(..)) => bail!("Cannot 'decrement' by a 'record'"),
            // If the key does not exist, set the starting value to 0.
            // Infer the starting type from the decrement type.
            None => match decrement {
                Literal::Address(..) => bail!("Cannot 'decrement' by an 'address'"),
                Literal::Boolean(..) => bail!("Cannot 'decrement' by a 'boolean'"),
                Literal::Field(..) => Literal::Field(Zero::zero()),
                Literal::Group(..) => Literal::Group(Zero::zero()),
                Literal::I8(..) => Literal::I8(Zero::zero()),
                Literal::I16(..) => Literal::I16(Zero::zero()),
                Literal::I32(..) => Literal::I32(Zero::zero()),
                Literal::I64(..) => Literal::I64(Zero::zero()),
                Literal::I128(..) => Literal::I128(Zero::zero()),
                Literal::U8(..) => Literal::U8(Zero::zero()),
                Literal::U16(..) => Literal::U16(Zero::zero()),
                Literal::U32(..) => Literal::U32(Zero::zero()),
                Literal::U64(..) => Literal::U64(Zero::zero()),
                Literal::U128(..) => Literal::U128(Zero::zero()),
                Literal::Scalar(..) => Literal::Scalar(Zero::zero()),
                Literal::String(..) => bail!("Cannot 'decrement' by a 'string'"),
            },
        };

        // Decrement the value.
        let outcome = match (start, decrement) {
            (Literal::Field(a), Literal::Field(b)) => Literal::Field(a.sub(b)),
            (Literal::Group(a), Literal::Group(b)) => Literal::Group(a.sub(b)),
            (Literal::I8(a), Literal::I8(b)) => Literal::I8(a.sub(b)),
            (Literal::I16(a), Literal::I16(b)) => Literal::I16(a.sub(b)),
            (Literal::I32(a), Literal::I32(b)) => Literal::I32(a.sub(b)),
            (Literal::I64(a), Literal::I64(b)) => Literal::I64(a.sub(b)),
            (Literal::I128(a), Literal::I128(b)) => Literal::I128(a.sub(b)),
            (Literal::U8(a), Literal::U8(b)) => Literal::U8(a.sub(b)),
            (Literal::U16(a), Literal::U16(b)) => Literal::U16(a.sub(b)),
            (Literal::U32(a), Literal::U32(b)) => Literal::U32(a.sub(b)),
            (Literal::U64(a), Literal::U64(b)) => Literal::U64(a.sub(b)),
            (Literal::U128(a), Literal::U128(b)) => Literal::U128(a.sub(b)),
            (Literal::Scalar(a), Literal::Scalar(b)) => Literal::Scalar(a.sub(b)),
            (a, b) => bail!("Cannot 'decrement' '{a}' by '{b}'"),
        };

        // Construct the value.
        let value = Value::Plaintext(Plaintext::from(outcome));
        // Update the value in storage.
        store.update_key_value(stack.program_id(), &self.mapping, key, value)?;

        Ok(())
    }
}

impl<N: Network> Parser for Decrement<N> {
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

impl<N: Network> FromStr for Decrement<N> {
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

impl<N: Network> Debug for Decrement<N> {
    /// Prints the command as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Decrement<N> {
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

impl<N: Network> FromBytes for Decrement<N> {
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

impl<N: Network> ToBytes for Decrement<N> {
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
        let (string, decrement) = Decrement::<CurrentNetwork>::parse("decrement account[r0] by r1;").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(decrement.mapping, Identifier::from_str("account").unwrap());
        assert_eq!(decrement.operands().len(), 2, "The number of operands is incorrect");
        assert_eq!(decrement.first, Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(decrement.second, Operand::Register(Register::Locator(1)), "The second operand is incorrect");
    }
}
