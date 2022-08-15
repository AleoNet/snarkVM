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

impl<N: Network> Parser for MapValue<N> {
    /// Parses a string into the value statement of the form `value {name} as {register_type};`.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the name from the string.
        let (string, name) = Identifier::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "as" from the string.
        let (string, _) = tag("as")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the finalize type from the string.
        let (string, finalize_type) = FinalizeType::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;
        // Return the value statement.
        Ok((string, Self { name, finalize_type }))
    }
}

impl<N: Network> FromStr for MapValue<N> {
    type Err = Error;

    /// Parses a string into the value statement.
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

impl<N: Network> Debug for MapValue<N> {
    /// Prints the value as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for MapValue<N> {
    /// Prints the value statement as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(
            f,
            "{type_} {name} as {finalize_type};",
            type_ = Self::type_name(),
            name = self.name,
            finalize_type = self.finalize_type
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_value_parse() -> Result<()> {
        // Literal
        let value = MapValue::<CurrentNetwork>::parse("value abcd as field.public;").unwrap().1;
        assert_eq!(value.name(), &Identifier::<CurrentNetwork>::from_str("abcd")?);
        assert_eq!(value.finalize_type(), &FinalizeType::<CurrentNetwork>::from_str("field.public")?);

        Ok(())
    }

    #[test]
    fn test_value_display() {
        // Literal
        let value = MapValue::<CurrentNetwork>::parse("value abc as field.public;").unwrap().1;
        assert_eq!(format!("{}", value), "value abc as field.public;");
    }
}
