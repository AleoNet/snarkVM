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

use super::*;

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
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the register from the string.
        let (string, register) = map_res(Register::parse, |register| {
            // Ensure the register is not a register member.
            match &register {
                Register::Locator(..) => Ok(register),
                Register::Member(..) => Err(error(format!("Input register {register} cannot be a register member"))),
            }
        })(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "as" from the string.
        let (string, _) = tag("as")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the value type from the string.
        let (string, value_type) = ValueType::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
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

impl<N: Network> Debug for Input<N> {
    /// Prints the input as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Input<N> {
    /// Prints the input statement as a string.
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

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_input_parse() -> Result<()> {
        // Literal
        let input = Input::<CurrentNetwork>::parse("input r0 as field.private;").unwrap().1;
        assert_eq!(input.register(), &Register::<CurrentNetwork>::Locator(0));
        assert_eq!(input.value_type(), &ValueType::<CurrentNetwork>::from_str("field.private")?);

        // Interface
        let input = Input::<CurrentNetwork>::parse("input r1 as signature.private;").unwrap().1;
        assert_eq!(input.register(), &Register::<CurrentNetwork>::Locator(1));
        assert_eq!(input.value_type(), &ValueType::<CurrentNetwork>::from_str("signature.private")?);

        // Record
        let input = Input::<CurrentNetwork>::parse("input r2 as token.record;").unwrap().1;
        assert_eq!(input.register(), &Register::<CurrentNetwork>::Locator(2));
        assert_eq!(input.value_type(), &ValueType::<CurrentNetwork>::from_str("token.record")?);

        Ok(())
    }

    #[test]
    fn test_input_display() -> Result<()> {
        // Literal
        let input = Input::<CurrentNetwork>::from_str("input r0 as field.private;")?;
        assert_eq!("input r0 as field.private;", input.to_string());

        // Interface
        let input = Input::<CurrentNetwork>::from_str("input r1 as signature.private;")?;
        assert_eq!("input r1 as signature.private;", input.to_string());

        // Record
        let input = Input::<CurrentNetwork>::parse("input r2 as token.record;").unwrap().1;
        assert_eq!(format!("{}", input), "input r2 as token.record;");

        Ok(())
    }
}
