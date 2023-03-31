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
use circuit::Assignment;

impl<N: Network> Parser for Table<N> {
    /// Parses a string into a table.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the 'table' keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the table name from the string.
        let (string, name) = Identifier::<N>::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the colon ':' keyword from the string.
        let (string, _) = tag(":")(string)?;

        // Parse the input statements from the string.
        let (string, inputs) = many1(TableInput::parse)(string)?;
        // Parse the output statements from the string.
        let (string, outputs) = many0(TableOutput::parse)(string)?;
        // Parse the entries from the string.
        let (string, entries) = many1(Entry::parse)(string)?;

        // Return the table.
        Ok((string, Self::new(name, inputs, outputs, entries)))
    }
}

impl<N: Network> FromStr for Table<N> {
    type Err = Error;

    /// Returns a table from a string literal.
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
    /// Prints the table as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Table<N> {
    /// Prints the table as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Write the table to a string.
        write!(f, "{} {}:", Self::type_name(), self.name)?;
        for input in &self.inputs {
            write!(f, "\n    {}", input)?;
        }
        for output in &self.outputs {
            write!(f, "\n    {}", output)?;
        }
        for entry in &self.entries {
            write!(f, "\n    {}", entry)?;
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
    fn test_table_parse() {
        let table = Table::<CurrentNetwork>::parse(
            r"table foo:
    input field;
    output u8;
    entry 0field to 0u8;
    entry 1field to 1u8;",
        )
        .unwrap()
        .1;
        assert_eq!("foo", table.name().to_string());
        assert_eq!("field", table.inputs[0].type_().to_string());
        assert_eq!("u8", table.outputs[0].type_().to_string());
        assert_eq!("entry 0field to 0u8", table.entries[0].to_string());
        assert_eq!("entry 1field to 1u8", table.entries[1].to_string());
    }

    #[test]
    fn test_table_display() {
        let expected = r"table foo:
    input field;
    output u8;
    entry 0field to 0u8;
    entry 1field to 1u8;";
        let table = Table::<CurrentNetwork>::parse(expected).unwrap().1;
        assert_eq!(expected, format!("{table}"),);
    }
}
