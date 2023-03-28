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

impl<N: Network> Parser for TableInput<N> {
    /// Parses a string into a key statement of the form `input {plaintext_type};`.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the finalize type from the string.
        let (string, type_) = PlaintextType::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;
        // Return the key statement.
        Ok((string, Self { type_ }))
    }
}

impl<N: Network> FromStr for TableInput<N> {
    type Err = Error;

    /// Parses a string into the key statement.
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

impl<N: Network> Debug for TableInput<N> {
    /// Prints the key statement as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for TableInput<N> {
    /// Prints the key statement as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{opcode} {type_};", opcode = Self::type_name(), type_ = self.type_)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_key_parse() -> Result<()> {
        // Literal
        let input = TableInput::<CurrentNetwork>::parse("input field;").unwrap().1;
        assert_eq!(input.type_(), &PlaintextType::<CurrentNetwork>::from_str("field")?);

        Ok(())
    }

    #[test]
    fn test_key_display() -> Result<()> {
        // Literal
        let input = TableInput::<CurrentNetwork>::from_str("input field;")?;
        assert_eq!("input field;", input.to_string());

        Ok(())
    }
}
