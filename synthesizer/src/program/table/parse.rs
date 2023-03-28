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

use super::*;

impl<N: Network> Parser for Table<N> {
    /// Parses a string into a table.
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

        // Parse the input statements from the string.
        let (string, inputs) = many1(TableInput::parse)(string)?;
        // Parse the output statements from the string.
        let (string, outputs) = many0(TableOutput::parse)(string)?;

        // Return the mapping.
        Ok((string, Self::new(name, inputs, outputs)))
    }
}

impl<N: Network> FromStr for Table<N> {
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

impl<N: Network> Debug for Table<N> {
    /// Prints the mapping as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Table<N> {
    /// Prints the mapping as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Write the mapping to a string.
        write!(f, "{} {}:", Self::type_name(), self.name)?;
        for input in &self.inputs {
            write!(f, "\n    {}", input)?;
        }
        for output in &self.outputs {
            write!(f, "\n    {}", output)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_mapping_parse() {
        let mapping = Table::<CurrentNetwork>::parse(
            r"
table foo:
    input field;
    output u8;",
        )
        .unwrap()
        .1;
        assert_eq!("foo", mapping.name().to_string());
        assert_eq!("field", mapping.inputs[0].type_().to_string());
        assert_eq!("u8", mapping.outputs[0].type_().to_string());
    }

    #[test]
    fn test_mapping_display() {
        let expected = r"
table foo:
    input field;
    output u8;";
        let mapping = Table::<CurrentNetwork>::parse(expected).unwrap().1;
        assert_eq!(expected, format!("{mapping}"),);
    }
}
