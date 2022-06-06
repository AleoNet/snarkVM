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

impl<N: Network> Parser for Interface<N> {
    /// Parses a string into an identifier.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        /// Parses a interface as `{ identifier_0: interface_0, ..., identifier_n: interface_n }`.
        fn parse_composite<N: Network>(string: &str) -> ParserResult<Interface<N>> {
            /// Parses a sanitized composite tuple.
            fn parse_composite_tuple<N: Network>(string: &str) -> ParserResult<(Identifier<N>, Interface<N>)> {
                // Parse the whitespace and comments from the string.
                let (string, _) = Sanitizer::parse(string)?;
                // Parse the identifier from the string.
                let (string, identifier) = Identifier::parse(string)?;
                // Parse the ":" from the string.
                let (string, _) = tag(":")(string)?;
                // Parse the interface from the string.
                let (string, interface) = Interface::parse(string)?;
                // Return the identifier and interface.
                Ok((string, (identifier, interface)))
            }

            // Parse the whitespace and comments from the string.
            let (string, _) = Sanitizer::parse(string)?;
            // Parse the "{" from the string.
            let (string, _) = tag("{")(string)?;
            // Parse the composites.
            let (string, composites) =
                map_res(separated_list1(tag(","), parse_composite_tuple), |composites: Vec<_>| {
                    // Ensure the number of composites is within `N::MAX_DATA_ENTRIES`.
                    match composites.len() <= N::MAX_DATA_ENTRIES {
                        true => Ok(composites),
                        false => Err(error(format!("Found an interface that exceeds size ({})", composites.len()))),
                    }
                })(string)?;
            // Parse the whitespace and comments from the string.
            let (string, _) = Sanitizer::parse(string)?;
            // Parse the '}' from the string.
            let (string, _) = tag("}")(string)?;
            // Output the interface.
            Ok((string, Interface::Composite(composites)))
        }

        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse to determine the interface (order matters).
        alt((
            // Parse a interface literal.
            map(LiteralType::parse, |literal| Self::Literal(literal)),
            // Parse a interface composite.
            parse_composite,
        ))(string)
    }
}

impl<N: Network> FromStr for Interface<N> {
    type Err = Error;

    /// Returns an interface from a string literal.
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

impl<N: Network> Debug for Interface<N> {
    /// Prints the interface as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

#[allow(clippy::format_push_string)]
impl<N: Network> Display for Interface<N> {
    /// Prints the interface as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            // Prints the literal, i.e. 10field
            Self::Literal(literal) => Display::fmt(literal, f),
            // Prints the composite, i.e. { owner: aleo1xxx.public, balance: 10i64.private }
            Self::Composite(composite) => {
                let mut output = format!("{{ ");
                for (identifier, interface) in composite.iter() {
                    output += &format!("{identifier}: {interface}, ");
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
    use crate::data::identifier::tests::sample_identifier;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: usize = 100;

    #[test]
    fn test_parse() -> Result<()> {
        // Sanity check.
        let (remainder, candidate) = Interface::<CurrentNetwork>::parse("{ foo: u8 }")?;
        assert_eq!("{ foo: u8 }", candidate.to_string());
        assert_eq!("", remainder);

        Ok(())
    }

    #[test]
    fn test_parse_fails() {
        // Must be non-empty.
        assert!(Interface::<CurrentNetwork>::parse("").is_err());
        assert!(Interface::<CurrentNetwork>::parse("{}").is_err());

        // Invalid characters.
        assert!(Interface::<CurrentNetwork>::parse("_").is_err());
        assert!(Interface::<CurrentNetwork>::parse("__").is_err());
        assert!(Interface::<CurrentNetwork>::parse("___").is_err());
        assert!(Interface::<CurrentNetwork>::parse("-").is_err());
        assert!(Interface::<CurrentNetwork>::parse("--").is_err());
        assert!(Interface::<CurrentNetwork>::parse("---").is_err());
        assert!(Interface::<CurrentNetwork>::parse("*").is_err());
        assert!(Interface::<CurrentNetwork>::parse("**").is_err());
        assert!(Interface::<CurrentNetwork>::parse("***").is_err());

        // Must not start with a number.
        assert!(Interface::<CurrentNetwork>::parse("1").is_err());
        assert!(Interface::<CurrentNetwork>::parse("2").is_err());
        assert!(Interface::<CurrentNetwork>::parse("3").is_err());
        assert!(Interface::<CurrentNetwork>::parse("1foo").is_err());
        assert!(Interface::<CurrentNetwork>::parse("12").is_err());
        assert!(Interface::<CurrentNetwork>::parse("111").is_err());

        // Must fit within the data capacity of a base field element.
        let interface =
            Interface::<CurrentNetwork>::parse("foo_bar_baz_qux_quux_quuz_corge_grault_garply_waldo_fred_plugh_xyzzy");
        assert!(interface.is_err());
    }
}
