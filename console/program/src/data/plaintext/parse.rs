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

// impl<N: Network> Parser for Plaintext<N> {
//     /// Parses a string into an identifier.
//     #[inline]
//     fn parse(string: &str) -> ParserResult<Self> {
//         /// Parses a plaintext as `{ identifier_0: plaintext_0, ..., identifier_n: plaintext_n }`.
//         fn parse_composite<N: Network>(string: &str) -> ParserResult<Plaintext<N>> {
//             /// Parses a sanitized composite tuple.
//             fn parse_composite_tuple<N: Network>(string: &str) -> ParserResult<(Identifier<N>, Plaintext<N>)> {
//                 // Parse the whitespace and comments from the string.
//                 let (string, _) = Sanitizer::parse(string)?;
//                 // Parse the identifier from the string.
//                 let (string, identifier) = Identifier::parse(string)?;
//                 // Parse the ":" from the string.
//                 let (string, _) = tag(":")(string)?;
//                 // Parse the plaintext from the string.
//                 let (string, plaintext) = Plaintext::parse(string)?;
//                 // Return the identifier and plaintext.
//                 Ok((string, (identifier, plaintext)))
//             }
//
//             // Parse the whitespace and comments from the string.
//             let (string, _) = Sanitizer::parse(string)?;
//             // Parse the "{" from the string.
//             let (string, _) = tag("{")(string)?;
//             // Parse the composites.
//             let (string, composites) =
//                 map_res(separated_list1(tag(","), parse_composite_tuple), |composites: Vec<_>| {
//                     // Ensure the number of composites is within `N::MAX_DATA_ENTRIES`.
//                     match composites.len() <= N::MAX_DATA_ENTRIES {
//                         true => Ok(composites),
//                         false => Err(error(format!("Found a plaintext that exceeds size ({})", composites.len()))),
//                     }
//                 })(string)?;
//             // Parse the whitespace and comments from the string.
//             let (string, _) = Sanitizer::parse(string)?;
//             // Parse the '}' from the string.
//             let (string, _) = tag("}")(string)?;
//             // Output the plaintext.
//             Ok((string, Plaintext::Composite(composites, Default::default())))
//         }
//
//         // Parse to determine the plaintext (order matters).
//         alt((
//             // Parse a plaintext literal.
//             map(Literal::parse, |literal| Self::Literal(literal, Default::default())),
//             // Parse a plaintext composite.
//             parse_composite,
//         ))(string)
//     }
// }

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
            // Prints the composite, i.e. { owner: aleo1xxx.public, balance: 10i64.private }
            Self::Composite(composite, ..) => {
                let mut output = format!("{{ ");
                for (identifier, plaintext) in composite.iter() {
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
    use crate::data::identifier::tests::sample_identifier;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: usize = 100;

    #[test]
    fn test_parse() -> Result<()> {
        // Sanity check.
        let (remainder, candidate) = Plaintext::<CurrentNetwork>::parse("{ foo: u8 }")?;
        assert_eq!("{ foo: u8 }", candidate.to_string());
        assert_eq!("", remainder);

        // // Must be alphanumeric or underscore.
        // let (remainder, candidate) = Plaintext::<CurrentNetwork>::parse("foo_bar~baz")?;
        // assert_eq!("foo_bar", candidate.to_string());
        // assert_eq!("~baz", remainder);
        //
        // // Must be alphanumeric or underscore.
        // let (remainder, candidate) = Plaintext::<CurrentNetwork>::parse("foo_bar-baz")?;
        // assert_eq!("foo_bar", candidate.to_string());
        // assert_eq!("-baz", remainder);
        //
        // // Check random identifiers.
        // for _ in 0..ITERATIONS {
        //     // Sample a random fixed-length alphanumeric string, that always starts with an alphabetic character.
        //     let expected_string = sample_identifier::<CurrentNetwork>()?;
        //     // Recover the field element from the bits.
        //     let expected_field = <CurrentNetwork as Network>::field_from_bits_le(&expected_string.to_bits_le())?;
        //
        //     let (remainder, candidate) = Plaintext::<CurrentNetwork>::parse(expected_string.as_str()).unwrap();
        //     assert_eq!(expected_string, candidate.to_string());
        //     assert_eq!(expected_field, candidate.0);
        //     assert_eq!(expected_string.len(), candidate.1 as usize);
        //     assert_eq!("", remainder);
        // }
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
