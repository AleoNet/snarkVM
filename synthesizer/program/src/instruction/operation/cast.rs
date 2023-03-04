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
    program::{Register, RegisterType},
};

/// Casts the operands into the declared type.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Cast<N: Network> {
    /// The operands.
    operands: Vec<Operand<N>>,
    /// The destination register.
    destination: Register<N>,
    /// The casted register type.
    register_type: RegisterType<N>,
}

impl<N: Network> Cast<N> {
    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        Opcode::Cast
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> &[Operand<N>] {
        &self.operands
    }

    /// Returns the destination register.
    #[inline]
    pub fn destinations(&self) -> Vec<Register<N>> {
        vec![self.destination.clone()]
    }

    /// Returns the casted register type.
    #[inline]
    pub const fn register_type(&self) -> &RegisterType<N> {
        &self.register_type
    }
}

impl<N: Network> Parser for Cast<N> {
    /// Parses a string into an operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        /// Parses an operand from the string.
        fn parse_operand<N: Network>(string: &str) -> ParserResult<Operand<N>> {
            // Parse the whitespace from the string.
            let (string, _) = Sanitizer::parse_whitespaces(string)?;
            // Parse the operand from the string.
            Operand::parse(string)
        }

        // Parse the opcode from the string.
        let (string, _) = tag(*Self::opcode())(string)?;
        // Parse the operands from the string.
        let (string, operands) = many1(parse_operand)(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "into" from the string.
        let (string, _) = tag("into")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the destination register from the string.
        let (string, destination) = Register::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "as" from the string.
        let (string, _) = tag("as")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the register type from the string.
        let (string, register_type) = RegisterType::parse(string)?;
        // Check that the number of operands does not exceed the maximum number of data entries.
        let max_operands = match register_type {
            RegisterType::Plaintext(_) => N::MAX_DATA_ENTRIES,
            // Note that if the register type is a record, then we must account for `owner` and `gates` which are not data entries.
            RegisterType::Record(_) | RegisterType::ExternalRecord(_) => N::MAX_DATA_ENTRIES + 2,
        };
        match operands.len() <= max_operands {
            true => Ok((string, Self { operands, destination, register_type })),
            false => {
                map_res(fail, |_: ParserResult<Self>| Err(error("Failed to parse 'cast' opcode: too many operands")))(
                    string,
                )
            }
        }
    }
}

impl<N: Network> FromStr for Cast<N> {
    type Err = Error;

    /// Parses a string into an operation.
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

impl<N: Network> Debug for Cast<N> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Cast<N> {
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Ensure the number of operands is within the bounds.
        let max_operands = match self.register_type() {
            RegisterType::Plaintext(_) => N::MAX_DATA_ENTRIES,
            // Note that if the register type is a record, then we must account for `owner` and `gates` which are not data entries.
            RegisterType::Record(_) | RegisterType::ExternalRecord(_) => N::MAX_DATA_ENTRIES + 2,
        };
        if self.operands.len().is_zero() || self.operands.len() > max_operands {
            eprintln!("The number of operands must be nonzero and <= {max_operands}");
            return Err(fmt::Error);
        }
        // Print the operation.
        write!(f, "{} ", Self::opcode())?;
        self.operands.iter().try_for_each(|operand| write!(f, "{operand} "))?;
        write!(f, "into {} as {}", self.destination, self.register_type)
    }
}

impl<N: Network> FromBytes for Cast<N> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the number of operands.
        let num_operands = u8::read_le(&mut reader)? as usize;

        // Ensure that the number of operands does not exceed the upper bound.
        // Note: although a similar check is performed later, this check is performed to ensure that an exceedingly large number of operands is not allocated.
        if num_operands.is_zero() || num_operands > N::MAX_DATA_ENTRIES + 2 {
            return Err(error(format!("The number of operands must be nonzero and <= {}", N::MAX_DATA_ENTRIES + 2)));
        }

        // Initialize the vector for the operands.
        let mut operands = Vec::with_capacity(num_operands);
        // Read the operands.
        for _ in 0..num_operands {
            operands.push(Operand::read_le(&mut reader)?);
        }

        // Read the destination register.
        let destination = Register::read_le(&mut reader)?;

        // Read the casted register type.
        let register_type = RegisterType::read_le(&mut reader)?;

        // Ensure the number of operands is within the bounds for the register type.
        let max_operands = match register_type {
            RegisterType::Plaintext(_) => N::MAX_DATA_ENTRIES,
            // Note that if the register type is a record, then we must account for `owner` and `gates` which are not data entries.
            RegisterType::Record(_) | RegisterType::ExternalRecord(_) => N::MAX_DATA_ENTRIES + 2,
        };
        if num_operands.is_zero() || num_operands > max_operands {
            return Err(error(format!("The number of operands must be nonzero and <= {max_operands}")));
        }

        // Return the operation.
        Ok(Self { operands, destination, register_type })
    }
}

impl<N: Network> ToBytes for Cast<N> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of operands is within the bounds.
        let max_operands = match self.register_type() {
            RegisterType::Plaintext(_) => N::MAX_DATA_ENTRIES,
            // Note that if the register type is a record, then we must account for `owner` and `gates` which are not data entries.
            RegisterType::Record(_) | RegisterType::ExternalRecord(_) => N::MAX_DATA_ENTRIES + 2,
        };
        if self.operands.len().is_zero() || self.operands.len() > max_operands {
            return Err(error(format!("The number of operands must be nonzero and <= {max_operands}")));
        }

        // Write the number of operands.
        (self.operands.len() as u8).write_le(&mut writer)?;
        // Write the operands.
        self.operands.iter().try_for_each(|operand| operand.write_le(&mut writer))?;
        // Write the destination register.
        self.destination.write_le(&mut writer)?;
        // Write the casted register type.
        self.register_type.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::{
        network::Testnet3,
        program::{Identifier, PlaintextType},
    };

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_parse() {
        let (string, cast) =
            Cast::<CurrentNetwork>::parse("cast r0.owner r0.gates r0.token_amount into r1 as token.record").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(cast.operands.len(), 3, "The number of operands is incorrect");
        assert_eq!(
            cast.operands[0],
            Operand::Register(Register::Member(0, vec![Identifier::from_str("owner").unwrap()])),
            "The first operand is incorrect"
        );
        assert_eq!(
            cast.operands[1],
            Operand::Register(Register::Member(0, vec![Identifier::from_str("gates").unwrap()])),
            "The second operand is incorrect"
        );
        assert_eq!(
            cast.operands[2],
            Operand::Register(Register::Member(0, vec![Identifier::from_str("token_amount").unwrap()])),
            "The third operand is incorrect"
        );
        assert_eq!(cast.destination, Register::Locator(1), "The destination register is incorrect");
        assert_eq!(
            cast.register_type,
            RegisterType::Record(Identifier::from_str("token").unwrap()),
            "The value type is incorrect"
        );
    }

    #[test]
    fn test_parse_cast_into_plaintext_max_operands() {
        let mut string = "cast ".to_string();
        let mut operands = Vec::with_capacity(CurrentNetwork::MAX_DATA_ENTRIES);
        for i in 0..CurrentNetwork::MAX_DATA_ENTRIES {
            string.push_str(&format!("r{i} "));
            operands.push(Operand::Register(Register::Locator(i as u64)));
        }
        string.push_str(&format!("into r{} as foo", CurrentNetwork::MAX_DATA_ENTRIES));
        let (string, cast) = Cast::<CurrentNetwork>::parse(&string).unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(cast.operands.len(), CurrentNetwork::MAX_DATA_ENTRIES, "The number of operands is incorrect");
        assert_eq!(cast.operands, operands, "The operands are incorrect");
        assert_eq!(
            cast.destination,
            Register::Locator(CurrentNetwork::MAX_DATA_ENTRIES as u64),
            "The destination register is incorrect"
        );
        assert_eq!(
            cast.register_type,
            RegisterType::Plaintext(PlaintextType::Struct(Identifier::from_str("foo").unwrap())),
            "The value type is incorrect"
        );
    }

    #[test]
    fn test_parse_cast_into_record_max_operands() {
        let mut string = "cast ".to_string();
        let mut operands = Vec::with_capacity(CurrentNetwork::MAX_DATA_ENTRIES + 2);
        for i in 0..CurrentNetwork::MAX_DATA_ENTRIES + 2 {
            string.push_str(&format!("r{i} "));
            operands.push(Operand::Register(Register::Locator(i as u64)));
        }
        string.push_str(&format!("into r{} as token.record", CurrentNetwork::MAX_DATA_ENTRIES + 2));
        let (string, cast) = Cast::<CurrentNetwork>::parse(&string).unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(cast.operands.len(), CurrentNetwork::MAX_DATA_ENTRIES + 2, "The number of operands is incorrect");
        assert_eq!(cast.operands, operands, "The operands are incorrect");
        assert_eq!(
            cast.destination,
            Register::Locator((CurrentNetwork::MAX_DATA_ENTRIES + 2) as u64),
            "The destination register is incorrect"
        );
        assert_eq!(
            cast.register_type,
            RegisterType::Record(Identifier::from_str("token").unwrap()),
            "The value type is incorrect"
        );
    }

    #[test]
    fn test_parse_cast_into_record_too_many_operands() {
        let mut string = "cast ".to_string();
        for i in 0..=CurrentNetwork::MAX_DATA_ENTRIES + 2 {
            string.push_str(&format!("r{i} "));
        }
        string.push_str(&format!("into r{} as token.record", CurrentNetwork::MAX_DATA_ENTRIES + 3));
        assert!(Cast::<CurrentNetwork>::parse(&string).is_err(), "Parser did not error");
    }

    #[test]
    fn test_parse_cast_into_plaintext_too_many_operands() {
        let mut string = "cast ".to_string();
        for i in 0..=CurrentNetwork::MAX_DATA_ENTRIES {
            string.push_str(&format!("r{i} "));
        }
        string.push_str(&format!("into r{} as foo", CurrentNetwork::MAX_DATA_ENTRIES + 1));
        assert!(Cast::<CurrentNetwork>::parse(&string).is_err(), "Parser did not error");
    }
}
