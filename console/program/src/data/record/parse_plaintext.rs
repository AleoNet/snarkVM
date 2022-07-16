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

impl<N: Network> Parser for Record<N, Plaintext<N>> {
    /// Parses a string as a record: `{ owner: address, gates: u64, identifier_0: entry_0, ..., identifier_n: entry_n }`.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        /// Parses a sanitized pair: `identifier: entry`.
        #[allow(clippy::type_complexity)]
        fn parse_pair<N: Network>(string: &str) -> ParserResult<(Identifier<N>, Entry<N, Plaintext<N>>)> {
            // Parse the whitespace and comments from the string.
            let (string, _) = Sanitizer::parse(string)?;
            // Parse the identifier from the string.
            let (string, identifier) = Identifier::parse(string)?;
            // Parse the ":" from the string.
            let (string, _) = tag(":")(string)?;
            // Parse the entry from the string.
            let (string, entry) = Entry::parse(string)?;
            // Return the identifier and entry.
            Ok((string, (identifier, entry)))
        }

        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the "{" from the string.
        let (string, _) = tag("{")(string)?;

        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the "owner" tag from the string.
        let (string, _) = tag("owner")(string)?;
        // Parse the ":" from the string.
        let (string, _) = tag(":")(string)?;
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the owner from the string.
        let (string, owner) = alt((
            map(pair(Address::parse, tag(".public")), |(owner, _)| Owner::Public(owner)),
            map(pair(Address::parse, tag(".private")), |(owner, _)| {
                Owner::Private(Plaintext::from(Literal::Address(owner)))
            }),
        ))(string)?;
        // Parse the "," from the string.
        let (string, _) = tag(",")(string)?;

        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the "gates" tag from the string.
        let (string, _) = tag("gates")(string)?;
        // Parse the ":" from the string.
        let (string, _) = tag(":")(string)?;
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the gates from the string.
        let (string, gates) = alt((
            map(pair(U64::parse, tag(".public")), |(gates, _)| Balance::Public(gates)),
            map(pair(U64::parse, tag(".private")), |(gates, _)| Balance::Private(Plaintext::from(Literal::U64(gates)))),
        ))(string)?;
        // Parse the "," from the string.
        let (string, has_entries) = opt(tag(","))(string)?;

        // Parse the entries.
        let (string, entries) = if has_entries.is_some() {
            map_res(separated_list0(tag(","), parse_pair), |entries: Vec<_>| {
                // Prepare the reserved entry names.
                let reserved = [
                    Identifier::from_str("owner").map_err(|e| error(e.to_string()))?,
                    Identifier::from_str("gates").map_err(|e| error(e.to_string()))?,
                ];
                // Ensure the entries has no duplicate names.
                if has_duplicates(entries.iter().map(|(identifier, _)| identifier).chain(reserved.iter())) {
                    return Err(error("Duplicate entry type found in record"));
                }
                // Ensure the number of interfaces is within `N::MAX_DATA_ENTRIES`.
                match entries.len() <= N::MAX_DATA_ENTRIES {
                    true => Ok(entries),
                    false => Err(error(format!("Found a record that exceeds size ({})", entries.len()))),
                }
            })(string)?
        } else {
            (string, Vec::new())
        };

        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the '}' from the string.
        let (string, _) = tag("}")(string)?;
        // Output the record.
        Ok((string, Record { owner, gates, data: IndexMap::from_iter(entries.into_iter()) }))
    }
}

impl<N: Network> FromStr for Record<N, Plaintext<N>> {
    type Err = Error;

    /// Returns a record from a string literal.
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

impl<N: Network> Debug for Record<N, Plaintext<N>> {
    /// Prints the record as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Record<N, Plaintext<N>> {
    /// Prints the record as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.fmt_internal(f, 0)
    }
}

impl<N: Network> Record<N, Plaintext<N>> {
    /// Prints the record with the given indentation depth.
    fn fmt_internal(&self, f: &mut Formatter, depth: usize) -> fmt::Result {
        /// The number of spaces to indent.
        const INDENT: usize = 2;

        // Print the opening brace.
        write!(f, "{{")?;
        // Print the owner with a comma.
        write!(f, "\n{:indent$}owner: {},", "", self.owner, indent = (depth + 1) * INDENT)?;
        // Print the gates with a comma.
        match self.data.is_empty() {
            // If the record data is empty, print the gates without a comma.
            true => write!(f, "\n{:indent$}gates: {}", "", self.gates, indent = (depth + 1) * INDENT)?,
            // If the record data is not empty, print the gates with a comma.
            false => write!(f, "\n{:indent$}gates: {},", "", self.gates, indent = (depth + 1) * INDENT)?,
        }
        // Print the data without a comma.
        for (i, (identifier, entry)) in self.data.iter().enumerate() {
            // Print the identifier.
            write!(f, "\n{:indent$}{identifier}: ", "", indent = (depth + 1) * INDENT)?;
            // Print the entry.
            match entry {
                // If the entry is a literal, print the entry without indentation.
                Entry::Constant(Plaintext::Literal(..))
                | Entry::Public(Plaintext::Literal(..))
                | Entry::Private(Plaintext::Literal(..)) => write!(f, "{entry}")?,
                // If the entry is an interface, print the entry with indentation.
                Entry::Constant(Plaintext::Interface(..))
                | Entry::Public(Plaintext::Interface(..))
                | Entry::Private(Plaintext::Interface(..)) => entry.fmt_internal(f, depth + 1)?,
            }
            // Print the comma, if this is not the last entry.
            if i != self.data.len() - 1 {
                write!(f, ",")?;
            }
        }
        // Print the closing brace.
        write!(f, "\n{:indent$}}}", "", indent = depth * INDENT)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_parse_without_data_entries() -> Result<()> {
        // Sanity check.
        let expected = r"{
  owner: aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.private,
  gates: 99u64.public
}";
        let given =
            "{ owner: aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.private, gates: 99u64.public }";
        let (remainder, candidate) = Record::<CurrentNetwork, Plaintext<CurrentNetwork>>::parse(given)?;
        println!("\nExpected: {expected}\n\nFound: {candidate}\n");
        assert_eq!(expected, candidate.to_string());
        assert_eq!("", remainder);
        Ok(())
    }

    #[test]
    fn test_parse_with_literal_entry() -> Result<()> {
        let expected = r"{
  owner: aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.public,
  gates: 99u64.private,
  foo: 5u8.constant
}";
        let given = "{ owner: aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.public, gates: 99u64.private, foo: 5u8.constant }";
        let (remainder, candidate) = Record::<CurrentNetwork, Plaintext<CurrentNetwork>>::parse(given)?;
        println!("\nExpected: {expected}\n\nFound: {candidate}\n");
        assert_eq!(expected, candidate.to_string());
        assert_eq!("", remainder);
        Ok(())
    }

    #[test]
    fn test_parse_with_interface_entry() -> Result<()> {
        let expected = r"{
  owner: aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.public,
  gates: 99u64.private,
  foo: 5u8.public,
  bar: {
    baz: 6u8.constant,
    qux: 7u8.constant
  },
  quux: 8u8.private,
  corge: {
    grault: 9u8.constant,
    garply: {
      waldo: 10u8.constant,
      fred: 11u8.constant
    }
  },
  xyzzy: {
    thud: 12u8.public
  }
}";
        let (remainder, candidate) = Record::<CurrentNetwork, Plaintext<CurrentNetwork>>::parse(expected)?;
        println!("\nExpected: {expected}\n\nFound: {candidate}\n");
        assert_eq!(expected, candidate.to_string());
        assert_eq!("", remainder);

        Ok(())
    }

    #[test]
    fn test_parse_fails() -> Result<()> {
        // Missing owner.
        let expected = "{ gates: 99u64.private, foo: 5u8.private }";
        assert!(Plaintext::<CurrentNetwork>::parse(expected).is_err());

        Ok(())
    }
}
