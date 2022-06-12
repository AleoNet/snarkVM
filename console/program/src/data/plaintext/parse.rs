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

impl<N: Network> Parser for Plaintext<N> {
    /// Parses a string into a plaintext value.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        /// Parses a plaintext as `{ identifier_0: plaintext_0, ..., identifier_n: plaintext_n }`.
        fn parse_interface<N: Network>(string: &str) -> ParserResult<Plaintext<N>> {
            /// Parses a sanitized interface tuple.
            fn parse_interface_tuple<N: Network>(string: &str) -> ParserResult<(Identifier<N>, Plaintext<N>)> {
                // Parse the whitespace and comments from the string.
                let (string, _) = Sanitizer::parse(string)?;
                // Parse the identifier from the string.
                let (string, identifier) = Identifier::parse(string)?;
                // Parse the ":" from the string.
                let (string, _) = tag(":")(string)?;
                // Parse the plaintext from the string.
                let (string, plaintext) = Plaintext::parse(string)?;
                // Return the identifier and plaintext.
                Ok((string, (identifier, plaintext)))
            }

            // Parse the whitespace and comments from the string.
            let (string, _) = Sanitizer::parse(string)?;
            // Parse the "{" from the string.
            let (string, _) = tag("{")(string)?;
            // Parse the members.
            let (string, members) = map_res(separated_list1(tag(","), parse_interface_tuple), |members: Vec<_>| {
                // Ensure the members has no duplicate names.
                if has_duplicates(members.iter().map(|(name, ..)| name)) {
                    return Err(error(format!("Duplicate member in interface")));
                }
                // Ensure the number of interfaces is within `N::MAX_DATA_ENTRIES`.
                match members.len() <= N::MAX_DATA_ENTRIES {
                    true => Ok(members),
                    false => Err(error(format!("Found a plaintext that exceeds size ({})", members.len()))),
                }
            })(string)?;
            // Parse the whitespace and comments from the string.
            let (string, _) = Sanitizer::parse(string)?;
            // Parse the '}' from the string.
            let (string, _) = tag("}")(string)?;
            // Output the plaintext.
            Ok((string, Plaintext::Interface(IndexMap::from_iter(members.into_iter()), Default::default())))
        }

        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse to determine the plaintext (order matters).
        alt((
            // Parse a plaintext literal.
            map(Literal::parse, |literal| Self::Literal(literal, Default::default())),
            // Parse a plaintext interface.
            parse_interface,
        ))(string)
    }
}

impl<N: Network> FromStr for Plaintext<N> {
    type Err = Error;

    /// Returns a plaintext from a string literal.
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

impl<N: Network> Debug for Plaintext<N> {
    /// Prints the plaintext as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

#[allow(clippy::format_push_string)]
impl<N: Network> Display for Plaintext<N> {
    /// Prints the plaintext as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            // Prints the literal, i.e. 10field
            Self::Literal(literal, ..) => Display::fmt(literal, f),
            // Prints the interface, i.e. { owner: aleo1xxx.public, balance: 10i64.private }
            Self::Interface(interface, ..) => {
                let mut output = format!("{{ ");
                for (identifier, plaintext) in interface.iter() {
                    output += &format!("{identifier}: {plaintext}, ");
                }
                output.pop(); // trailing space
                output.pop(); // trailing comma
                output += " }";
                write!(f, "{output}")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_parse() -> Result<()> {
        // Sanity check.
        let (remainder, candidate) = Plaintext::<CurrentNetwork>::parse("{ foo: 5u8 }")?;
        assert_eq!("{ foo: 5u8 }", candidate.to_string());
        assert_eq!("", remainder);

        Ok(())
    }

    #[test]
    fn test_parse_fails() {
        // Must be non-empty.
        assert!(Plaintext::<CurrentNetwork>::parse("").is_err());
        assert!(Plaintext::<CurrentNetwork>::parse("{}").is_err());

        // Invalid characters.
        assert!(Plaintext::<CurrentNetwork>::parse("_").is_err());
        assert!(Plaintext::<CurrentNetwork>::parse("__").is_err());
        assert!(Plaintext::<CurrentNetwork>::parse("___").is_err());
        assert!(Plaintext::<CurrentNetwork>::parse("-").is_err());
        assert!(Plaintext::<CurrentNetwork>::parse("--").is_err());
        assert!(Plaintext::<CurrentNetwork>::parse("---").is_err());
        assert!(Plaintext::<CurrentNetwork>::parse("*").is_err());
        assert!(Plaintext::<CurrentNetwork>::parse("**").is_err());
        assert!(Plaintext::<CurrentNetwork>::parse("***").is_err());

        // Must not start with a number.
        assert!(Plaintext::<CurrentNetwork>::parse("1").is_err());
        assert!(Plaintext::<CurrentNetwork>::parse("2").is_err());
        assert!(Plaintext::<CurrentNetwork>::parse("3").is_err());
        assert!(Plaintext::<CurrentNetwork>::parse("1foo").is_err());
        assert!(Plaintext::<CurrentNetwork>::parse("12").is_err());
        assert!(Plaintext::<CurrentNetwork>::parse("111").is_err());

        // Must fit within the data capacity of a base field element.
        let plaintext =
            Plaintext::<CurrentNetwork>::parse("foo_bar_baz_qux_quux_quuz_corge_grault_garply_waldo_fred_plugh_xyzzy");
        assert!(plaintext.is_err());
    }
}
