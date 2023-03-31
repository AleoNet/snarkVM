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

impl<N: Network> Parser for Entry<N> {
    /// Parses a string into a key statement of the form `entry {input}+ [to {output}*]?;`.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the finalize type from the string.
        let (string, inputs) =
            many1(map(pair(Literal::<N>::parse, Sanitizer::parse_whitespaces), |(literal, _)| literal))(string)?;
        // Optionally parse the `to` keyword from the string.
        let (string, outputs) = match opt(tag("to"))(string)? {
            (string, Some(_)) => {
                // Parse the whitespace from the string.
                let (string, _) = Sanitizer::parse_whitespaces(string)?;
                // Parse the finalize type from the string.
                let (string, outputs) = many1(map(
                    pair(Literal::<N>::parse, Sanitizer::parse_whitespaces),
                    |(literal, _)| literal,
                ))(string)?;
                (string, outputs)
            }
            (string, None) => (string, vec![]),
        };
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;
        // Return the key statement.
        Ok((string, Self { inputs, outputs }))
    }
}

impl<N: Network> FromStr for Entry<N> {
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

impl<N: Network> Debug for Entry<N> {
    /// Prints the key statement as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Entry<N> {
    /// Prints the key statement as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Print the operation.
        write!(f, "{} ", Self::type_name())?;
        self.inputs.iter().try_for_each(|input| write!(f, " {input}"))?;
        if !self.outputs.is_empty() {
            write!(f, " to")?;
            self.outputs.iter().try_for_each(|output| write!(f, " {output}"))?;
        }
        write!(f, ";")?;

        Ok(())
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
        let input = Entry::<CurrentNetwork>::parse("entry 1field to 2field;").unwrap().1;
        assert_eq!(input.inputs(), &[Literal::<CurrentNetwork>::from_str("1field")?]);
        assert_eq!(input.outputs(), &[Literal::<CurrentNetwork>::from_str("2field")?]);

        Ok(())
    }

    #[test]
    fn test_key_display() -> Result<()> {
        // Literal
        let input = Entry::<CurrentNetwork>::from_str("input 1field to 2field;")?;
        assert_eq!("entry 1field to 2field;", input.to_string());

        Ok(())
    }
}
