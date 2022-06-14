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

impl<N: Network> Parser for Entry<N, Plaintext<N>> {
    /// Parses a string into the entry.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        /// A helper enum encoding the visibility.
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
        enum Mode {
            Constant,
            Public,
            Private,
        }

        /// Parses an entry as a literal: `literal.visibility`.
        fn parse_literal<N: Network>(string: &str) -> ParserResult<(Plaintext<N>, Mode)> {
            alt((
                map(pair(Literal::parse, tag(".constant")), |(literal, _)| (Plaintext::from(literal), Mode::Constant)),
                map(pair(Literal::parse, tag(".public")), |(literal, _)| (Plaintext::from(literal), Mode::Public)),
                map(pair(Literal::parse, tag(".private")), |(literal, _)| (Plaintext::from(literal), Mode::Private)),
            ))(string)
        }

        /// Parses a sanitized pair: `identifier: entry`.
        fn parse_pair<N: Network>(string: &str) -> ParserResult<(Identifier<N>, Plaintext<N>, Mode)> {
            // Parse the whitespace and comments from the string.
            let (string, _) = Sanitizer::parse(string)?;
            // Parse the identifier from the string.
            let (string, identifier) = Identifier::parse(string)?;
            // Parse the whitespace from the string.
            let (string, _) = Sanitizer::parse_whitespaces(string)?;
            // Parse the ":" from the string.
            let (string, _) = tag(":")(string)?;
            // Parse the whitespace from the string.
            let (string, _) = Sanitizer::parse_whitespaces(string)?;
            // Parse the plaintext and visibility from the string.
            let (string, (plaintext, mode)) = alt((
                // Parse a literal.
                parse_literal,
                // Parse an interface.
                parse_interface,
            ))(string)?;
            // Return the identifier, plaintext, and visibility.
            Ok((string, (identifier, plaintext, mode)))
        }

        /// Parses an entry as an interface: `{ identifier_0: plaintext_0.visibility, ..., identifier_n: plaintext_n.visibility }`.
        /// Observe the `visibility` is the same for all members of the plaintext value.
        fn parse_interface<N: Network>(string: &str) -> ParserResult<(Plaintext<N>, Mode)> {
            // Parse the whitespace and comments from the string.
            let (string, _) = Sanitizer::parse(string)?;
            // Parse the "{" from the string.
            let (string, _) = tag("{")(string)?;
            // Parse the members.
            let (string, (members, mode)) = map_res(separated_list1(tag(","), parse_pair), |members: Vec<_>| {
                // Ensure the members has no duplicate names.
                if has_duplicates(members.iter().map(|(name, ..)| name)) {
                    return Err(error("Duplicate member in interface"));
                }
                // Ensure the members all have the same visibility.
                let mode = members.iter().map(|(_, _, mode)| mode).dedup().collect::<Vec<_>>();
                let mode = match mode.len() == 1 {
                    true => *mode[0],
                    false => return Err(error("Members of interface in entry have different visibilities")),
                };
                // Ensure the number of interfaces is within `N::MAX_DATA_ENTRIES`.
                match members.len() <= N::MAX_DATA_ENTRIES {
                    // Return the members and the visibility.
                    true => Ok((members.into_iter().map(|(i, p, _)| (i, p)).collect::<Vec<_>>(), mode)),
                    false => Err(error(format!("Found a plaintext that exceeds size ({})", members.len()))),
                }
            })(string)?;
            // Parse the whitespace and comments from the string.
            let (string, _) = Sanitizer::parse(string)?;
            // Parse the '}' from the string.
            let (string, _) = tag("}")(string)?;
            // Output the plaintext and visibility.
            Ok((string, (Plaintext::Interface(IndexMap::from_iter(members.into_iter()), Default::default()), mode)))
        }

        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse to determine the entry (order matters).
        let (string, (plaintext, mode)) = alt((
            // Parse a literal.
            parse_literal,
            // Parse an interface.
            parse_interface,
        ))(string)?;

        // Return the entry.
        match mode {
            Mode::Constant => Ok((string, Entry::Constant(plaintext))),
            Mode::Public => Ok((string, Entry::Public(plaintext))),
            Mode::Private => Ok((string, Entry::Private(plaintext))),
        }
    }
}

impl<N: Network> FromStr for Entry<N, Plaintext<N>> {
    type Err = Error;

    /// Returns the entry from a string literal.
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

impl<N: Network> Debug for Entry<N, Plaintext<N>> {
    /// Prints the entry as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Entry<N, Plaintext<N>> {
    /// Prints the entry as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.fmt_internal(f, 0)
    }
}

impl<N: Network> Entry<N, Plaintext<N>> {
    /// Prints the entry with the given indentation depth.
    pub(in crate::data::record) fn fmt_internal(&self, f: &mut Formatter, depth: usize) -> fmt::Result {
        /// The number of spaces to indent.
        const INDENT: usize = 2;

        let (plaintext, visibility) = match self {
            Self::Constant(constant) => (constant, "constant"),
            Self::Public(public) => (public, "public"),
            Self::Private(private) => (private, "private"),
        };

        match plaintext {
            // Prints the literal, i.e. 10field.public
            Plaintext::Literal(literal, ..) => {
                write!(f, "{:indent$}{literal}.{visibility}", "", indent = depth * INDENT)
            }
            // Prints the interface, i.e. { first: 10i64.private, second: 198u64.private }
            Plaintext::Interface(interface, ..) => {
                // Print the opening brace.
                write!(f, "{{")?;
                // Print the members.
                interface.iter().enumerate().try_for_each(|(i, (name, plaintext))| {
                    match plaintext {
                        #[rustfmt::skip]
                        Plaintext::Literal(literal, ..) => match i == interface.len() - 1 {
                            true => {
                                // Print the last member without a comma.
                                write!(f, "\n{:indent$}{name}: {literal}.{visibility}", "", indent = (depth + 1) * INDENT)?;
                                // Print the closing brace.
                                write!(f, "\n{:indent$}}}", "", indent = depth * INDENT)
                            }
                            // Print the member with a comma.
                            false => write!(f, "\n{:indent$}{name}: {literal}.{visibility},", "", indent = (depth + 1) * INDENT),
                        },
                        Plaintext::Interface(..) => {
                            // Print the member name.
                            write!(f, "\n{:indent$}{name}: ", "", indent = (depth + 1) * INDENT)?;
                            // Print the member.
                            match self {
                                Self::Constant(..) => Self::Constant(plaintext.clone()).fmt_internal(f, depth + 1)?,
                                Self::Public(..) => Self::Public(plaintext.clone()).fmt_internal(f, depth + 1)?,
                                Self::Private(..) => Self::Private(plaintext.clone()).fmt_internal(f, depth + 1)?,
                            }
                            // Print the closing brace.
                            match i == interface.len() - 1 {
                                // Print the last member without a comma.
                                true => write!(f, "\n{:indent$}}}", "", indent = depth * INDENT),
                                // Print the member with a comma.
                                false => write!(f, "\n{:indent$}}},", "", indent = depth * INDENT),
                            }
                        }
                    }
                })
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
        let expected = r"{
  foo: 5u8.private
}";
        let (remainder, candidate) = Entry::<CurrentNetwork, Plaintext<CurrentNetwork>>::parse("{ foo: 5u8.private }")?;
        assert_eq!(expected, candidate.to_string());
        assert_eq!("", remainder);

        let expected = r"{
  foo: 5u8.public,
  bar: {
    baz: 10field.public,
    qux: {
      quux: {
        corge: {
          grault: {
            garply: {
              waldo: {
                fred: {
                  plugh: {
                    xyzzy: {
                      thud: true.public
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}";
        let (remainder, candidate) = Entry::<CurrentNetwork, Plaintext<CurrentNetwork>>::parse(
            "{ foo: 5u8.public, bar: { baz: 10field.public, qux: {quux:{corge :{grault:  {garply:{waldo:{fred:{plugh:{xyzzy: { thud: true.public}} }}}  }}}}}}",
        )?;
        println!("\nExpected: {expected}\n\nFound: {candidate}\n");
        assert_eq!(expected, candidate.to_string());
        assert_eq!("", remainder);

        Ok(())
    }
}
