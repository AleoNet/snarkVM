// Copyright 2024 Aleo Network Foundation
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

use super::*;

impl<N: Network> Parser for MapValue<N> {
    /// Parses a string into a value statement of the form `value as {plaintext_type}.public;`.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "as" from the string.
        let (string, _) = tag("as")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the plaintext type from the string.
        let (string, (plaintext_type, _)) = pair(PlaintextType::parse, tag(".public"))(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;
        // Return the value statement.
        Ok((string, Self { plaintext_type }))
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
            "{type_} as {plaintext_type}.public;",
            type_ = Self::type_name(),
            plaintext_type = self.plaintext_type
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::MainnetV0;

    type CurrentNetwork = MainnetV0;

    #[test]
    fn test_value_parse() -> Result<()> {
        // Literal
        let value = MapValue::<CurrentNetwork>::parse("value as field.public;").unwrap().1;
        assert_eq!(value.plaintext_type(), &PlaintextType::<CurrentNetwork>::from_str("field")?);

        Ok(())
    }

    #[test]
    fn test_value_display() {
        // Literal
        let value = MapValue::<CurrentNetwork>::parse("value as field.public;").unwrap().1;
        assert_eq!(format!("{value}"), "value as field.public;");
    }
}
