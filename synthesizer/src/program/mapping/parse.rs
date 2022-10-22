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

impl<N: Network> Parser for Mapping<N> {
    /// Parses a string into a mapping.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the 'mapping' keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the mapping name from the string.
        let (string, name) = Identifier::<N>::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the colon ':' keyword from the string.
        let (string, _) = tag(":")(string)?;

        // Parse the key statement from the string.
        let (string, key) = MapKey::parse(string)?;
        // Parse the value statement from the string.
        let (string, value) = MapValue::parse(string)?;

        // Return the mapping.
        Ok((string, Self::new(name, key, value)))
    }
}

impl<N: Network> FromStr for Mapping<N> {
    type Err = Error;

    /// Returns a mapping from a string literal.
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

impl<N: Network> Debug for Mapping<N> {
    /// Prints the mapping as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Mapping<N> {
    /// Prints the mapping as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Write the mapping to a string.
        write!(f, "{} {}:", Self::type_name(), self.name)?;
        write!(f, "\n    {}", self.key)?;
        write!(f, "\n    {}", self.value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_mapping_parse() {
        let mapping = Mapping::<CurrentNetwork>::parse(
            r"
mapping foo:
    key a as field.public;
    value b as field.public;",
        )
        .unwrap()
        .1;
        assert_eq!("foo", mapping.name().to_string());
        assert_eq!("a", mapping.key.name().to_string());
        assert_eq!("field.public", mapping.key.finalize_type().to_string());
        assert_eq!("b", mapping.value.name().to_string());
        assert_eq!("field.public", mapping.value.finalize_type().to_string());
    }

    #[test]
    fn test_mapping_display() {
        let expected = r"mapping foo:
    key a as field.public;
    value b as field.public;";
        let mapping = Mapping::<CurrentNetwork>::parse(expected).unwrap().1;
        assert_eq!(expected, format!("{mapping}"),);
    }
}
