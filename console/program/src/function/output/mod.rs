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

use crate::{Register, Sanitizer, ValueType};
use snarkvm_console_network::prelude::*;
use snarkvm_utilities::{
    io::{Read, Result as IoResult, Write},
    FromBytes,
    ToBytes,
};

/// An output statement defines an output of a function, and may refer to the value
/// in either a register or a register member. An output statement is of the form
/// `output {register} as {value_type};`.
#[derive(PartialEq, Eq, Hash)]
pub struct Output<N: Network> {
    /// The output register.
    register: Register<N>,
    /// The output value type.
    value_type: ValueType<N>,
}

impl<N: Network> Output<N> {
    /// Returns the output register.
    #[inline]
    pub const fn register(&self) -> &Register<N> {
        &self.register
    }

    /// Returns the output value type.
    #[inline]
    pub const fn value_type(&self) -> &ValueType<N> {
        &self.value_type
    }
}

impl<N: Network> TypeName for Output<N> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "output"
    }
}

impl<N: Network> Parser for Output<N> {
    /// Parses a string into an output statement.
    /// The output statement is of the form `output {register} as {value_type};`.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the output keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the register from the string.
        let (string, register) = Register::parse(string)?;
        // Parse the " as " from the string.
        let (string, _) = tag(" as ")(string)?;
        // Parse the value type from the string.
        let (string, value_type) = ValueType::parse(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;
        // Return the output statement.
        Ok((string, Self { register, value_type }))
    }
}

impl<N: Network> FromStr for Output<N> {
    type Err = Error;

    /// Parses a string into an output statement.
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

impl<N: Network> Debug for Output<N> {
    /// Prints the output as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Output<N> {
    /// Prints the output statement as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(
            f,
            "{type_} {register} as {value_type};",
            type_ = Self::type_name(),
            register = self.register,
            value_type = self.value_type
        )
    }
}

impl<N: Network> FromBytes for Output<N> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let register = FromBytes::read_le(&mut reader)?;
        let value_type = FromBytes::read_le(&mut reader)?;
        Ok(Self { register, value_type })
    }
}

impl<N: Network> ToBytes for Output<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.register.write_le(&mut writer)?;
        self.value_type.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_output_type_name() {
        assert_eq!(Output::<CurrentNetwork>::type_name(), "output");
    }

    #[test]
    fn test_output_parse() -> Result<()> {
        // Literal
        let output = Output::<CurrentNetwork>::parse("output r0 as field.private;").unwrap().1;
        assert_eq!(output.register(), &Register::<CurrentNetwork>::Locator(0));
        assert_eq!(output.value_type(), &ValueType::<CurrentNetwork>::from_str("field.private")?);

        // Composite
        let output = Output::<CurrentNetwork>::parse("output r1 as signature.private;").unwrap().1;
        assert_eq!(output.register(), &Register::<CurrentNetwork>::Locator(1));
        assert_eq!(output.value_type(), &ValueType::<CurrentNetwork>::from_str("signature.private")?);

        Ok(())
    }

    #[test]
    fn test_output_display() {
        // Literal
        let output = Output::<CurrentNetwork>::parse("output r0 as field.private;").unwrap().1;
        assert_eq!(format!("{}", output), "output r0 as field.private;");

        // Composite
        let output = Output::<CurrentNetwork>::parse("output r1 as signature.private;").unwrap().1;
        assert_eq!(format!("{}", output), "output r1 as signature.private;");
    }
}
