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

use crate::{function::Register, Sanitizer, ValueType};
use snarkvm_console_network::prelude::*;
use snarkvm_utilities::{
    error,
    io::{Read, Result as IoResult, Write},
    FromBytes,
    ToBytes,
};

/// An input statement defines an input argument to a function, and is of the form
/// `input {register} as {value_type}`.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Input<N: Network> {
    /// The input register.
    register: Register<N>,
    /// The input value type.
    value_type: ValueType<N>,
}

impl<N: Network> Input<N> {
    /// Returns the input register.
    #[inline]
    pub fn register(&self) -> &Register<N> {
        &self.register
    }

    /// Returns the input value type.
    #[inline]
    pub fn value_type(&self) -> &ValueType<N> {
        &self.value_type
    }
}

impl<N: Network> TypeName for Input<N> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "input"
    }
}

impl<N: Network> Parser for Input<N> {
    /// Parses a string into an input statement.
    /// The input statement is of the form `input {register} as {value_type};`.
    ///
    /// # Errors
    /// This function will halt if the given register is a register member.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the input keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the register from the string.
        let (string, register) = map_res(Register::parse, |register| {
            // Ensure the register is not a register member.
            match &register {
                Register::Locator(..) => Ok(register),
                Register::Member(..) => Err(error(format!("Input register {register} cannot be a register member"))),
            }
        })(string)?;
        // Parse the " as " from the string.
        let (string, _) = tag(" as ")(string)?;
        // Parse the value type from the string.
        let (string, value_type) = ValueType::parse(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;
        // Return the input statement.
        Ok((string, Self { register, value_type }))
    }
}

impl<N: Network> FromStr for Input<N> {
    type Err = Error;

    /// Parses a string into an input statement.
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

impl<N: Network> fmt::Display for Input<N> {
    /// Prints the input statement as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{type_} {register} as {value_type};",
            type_ = Self::type_name(),
            register = self.register,
            value_type = self.value_type
        )
    }
}

impl<N: Network> FromBytes for Input<N> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let register = FromBytes::read_le(&mut reader)?;
        let value_type = FromBytes::read_le(&mut reader)?;
        Ok(Self { register, value_type })
    }
}

impl<N: Network> ToBytes for Input<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.register.write_le(&mut writer)?;
        self.value_type.write_le(&mut writer)
    }
}

impl<N: Network> Ord for Input<N> {
    /// Ordering is determined by the register (the value type is ignored).
    fn cmp(&self, other: &Self) -> Ordering {
        self.register().cmp(other.register())
    }
}

impl<N: Network> PartialOrd for Input<N> {
    /// Ordering is determined by the register (the value type is ignored).
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_input_type_name() -> Result<()> {
        assert_eq!(Input::<CurrentNetwork>::type_name(), "input");
        Ok(())
    }

    #[test]
    fn test_input_parse() -> Result<()> {
        // Literal
        let input = Input::<CurrentNetwork>::parse("input r0 as field.private;").unwrap().1;
        assert_eq!(input.register(), &Register::<CurrentNetwork>::Locator(0));
        assert_eq!(input.value_type(), &ValueType::<CurrentNetwork>::from_str("field.private")?);

        // Composite
        let input = Input::<CurrentNetwork>::parse("input r1 as signature.private;").unwrap().1;
        assert_eq!(input.register(), &Register::<CurrentNetwork>::Locator(1));
        assert_eq!(input.value_type(), &ValueType::<CurrentNetwork>::from_str("signature.private")?);

        Ok(())
    }

    #[test]
    fn test_input_display() -> Result<()> {
        // Literal
        let input = Input::<CurrentNetwork>::from_str("input r0 as field.private;")?;
        assert_eq!("input r0 as field.private;", input.to_string());

        // Composite
        let input = Input::<CurrentNetwork>::from_str("input r1 as signature.private;")?;
        assert_eq!("input r1 as signature.private;", input.to_string());

        Ok(())
    }

    #[test]
    fn test_input_partial_ord() -> Result<()> {
        let input1 = Input::<CurrentNetwork>::from_str("input r0 as field.private;")?;
        let input2 = Input::<CurrentNetwork>::from_str("input r1 as field.private;")?;

        let input3 = Input::<CurrentNetwork>::from_str("input r0 as signature.private;")?;
        let input4 = Input::<CurrentNetwork>::from_str("input r1 as signature.private;")?;

        assert_eq!(input1.partial_cmp(&input1), Some(Ordering::Equal));
        assert_eq!(input1.partial_cmp(&input2), Some(Ordering::Less));
        assert_eq!(input1.partial_cmp(&input3), Some(Ordering::Equal));
        assert_eq!(input1.partial_cmp(&input4), Some(Ordering::Less));

        assert_eq!(input2.partial_cmp(&input1), Some(Ordering::Greater));
        assert_eq!(input2.partial_cmp(&input2), Some(Ordering::Equal));
        assert_eq!(input2.partial_cmp(&input3), Some(Ordering::Greater));
        assert_eq!(input2.partial_cmp(&input4), Some(Ordering::Equal));

        assert_eq!(input3.partial_cmp(&input1), Some(Ordering::Equal));
        assert_eq!(input3.partial_cmp(&input2), Some(Ordering::Less));
        assert_eq!(input3.partial_cmp(&input3), Some(Ordering::Equal));
        assert_eq!(input3.partial_cmp(&input4), Some(Ordering::Less));

        assert_eq!(input4.partial_cmp(&input1), Some(Ordering::Greater));
        assert_eq!(input4.partial_cmp(&input2), Some(Ordering::Equal));
        assert_eq!(input4.partial_cmp(&input3), Some(Ordering::Greater));
        assert_eq!(input4.partial_cmp(&input4), Some(Ordering::Equal));

        Ok(())
    }
}
