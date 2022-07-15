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

impl<N: Network> Parser for RecordType<N> {
    /// Parses a record type as:
    /// ```text
    ///   record message:
    ///       owner as address.private;
    ///       gates as u64.public;
    /// ```
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        /// Parses a string into a tuple.
        fn parse_entry<N: Network>(string: &str) -> ParserResult<(Identifier<N>, EntryType<N>)> {
            // Parse the whitespace and comments from the string.
            let (string, _) = Sanitizer::parse(string)?;
            // Parse the identifier from the string.
            let (string, identifier) = Identifier::parse(string)?;
            // Parse the whitespace from the string.
            let (string, _) = Sanitizer::parse_whitespaces(string)?;
            // Parse the "as" from the string.
            let (string, _) = tag("as")(string)?;
            // Parse the whitespace from the string.
            let (string, _) = Sanitizer::parse_whitespaces(string)?;
            // Parse the value type from the string.
            let (string, value_type) = EntryType::parse(string)?;
            // Parse the whitespace from the string.
            let (string, _) = Sanitizer::parse_whitespaces(string)?;
            // Parse the semicolon ';' keyword from the string.
            let (string, _) = tag(";")(string)?;
            // Return the identifier and value type.
            Ok((string, (identifier, value_type)))
        }

        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the type name from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the record name from the string.
        let (string, name) = Identifier::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the colon ':' keyword from the string.
        let (string, _) = tag(":")(string)?;

        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the "owner" tag from the string.
        let (string, _) = tag("owner")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "as" from the string.
        let (string, _) = tag("as")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the owner visibility from the string.
        let (string, owner) = alt((
            map(tag("address.public"), |_| PublicOrPrivate::Public),
            map(tag("address.private"), |_| PublicOrPrivate::Private),
        ))(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the ";" from the string.
        let (string, _) = tag(";")(string)?;

        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the "gates" tag from the string.
        let (string, _) = tag("gates")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "as" from the string.
        let (string, _) = tag("as")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the gates visibility from the string.
        let (string, gates) = alt((
            map(tag("u64.public"), |_| PublicOrPrivate::Public),
            map(tag("u64.private"), |_| PublicOrPrivate::Private),
        ))(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the ";" from the string.
        let (string, _) = tag(";")(string)?;

        // Parse the entries from the string.
        let (string, entries) = map_res(many0(parse_entry), |entries| {
            // Prepare the reserved entry names.
            let reserved = [
                Identifier::from_str("owner").map_err(|e| error(e.to_string()))?,
                Identifier::from_str("gates").map_err(|e| error(e.to_string()))?,
            ];
            // Ensure the entries has no duplicate names.
            if has_duplicates(entries.iter().map(|(identifier, _)| identifier).chain(reserved.iter())) {
                return Err(error(format!("Duplicate entry type found in record '{}'", name)));
            }
            // Ensure the number of members is within `N::MAX_DATA_ENTRIES`.
            if entries.len() > N::MAX_DATA_ENTRIES {
                return Err(error("Failed to parse record: too many entries"));
            }
            Ok(entries)
        })(string)?;

        // Return the record type.
        Ok((string, Self { name, owner, gates, entries: IndexMap::from_iter(entries.into_iter()) }))
    }
}

impl<N: Network> FromStr for RecordType<N> {
    type Err = Error;

    /// Returns an record type from a string literal.
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

impl<N: Network> Debug for RecordType<N> {
    /// Prints the record type as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for RecordType<N> {
    /// Prints the record type as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{} {}:", Self::type_name(), self.name)?;
        write!(f, "\n    owner as address.{};", self.owner)?;
        write!(f, "\n    gates as u64.{};", self.gates)?;
        self.entries.iter().try_for_each(|(entry_name, entry_type)| write!(f, "\n    {entry_name} as {entry_type};"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_parse() -> Result<()> {
        let expected = RecordType::<CurrentNetwork> {
            name: Identifier::from_str("message")?,
            owner: PublicOrPrivate::Private,
            gates: PublicOrPrivate::Public,
            entries: IndexMap::from_iter(
                vec![(Identifier::from_str("first")?, EntryType::from_str("field.constant")?)].into_iter(),
            ),
        };

        let (remainder, candidate) = RecordType::<CurrentNetwork>::parse(
            r"
record message:
    owner as address.private;
    gates as u64.public;
    first as field.constant;
",
        )?;
        assert_eq!("\n", remainder);
        assert_eq!(expected, candidate);
        Ok(())
    }

    #[test]
    fn test_parse_fails() {
        // Must be non-empty.
        assert!(RecordType::<CurrentNetwork>::parse("").is_err());
        assert!(RecordType::<CurrentNetwork>::parse("record message:").is_err());

        // Invalid characters.
        assert!(RecordType::<CurrentNetwork>::parse("{}").is_err());
        assert!(RecordType::<CurrentNetwork>::parse("_").is_err());
        assert!(RecordType::<CurrentNetwork>::parse("__").is_err());
        assert!(RecordType::<CurrentNetwork>::parse("___").is_err());
        assert!(RecordType::<CurrentNetwork>::parse("-").is_err());
        assert!(RecordType::<CurrentNetwork>::parse("--").is_err());
        assert!(RecordType::<CurrentNetwork>::parse("---").is_err());
        assert!(RecordType::<CurrentNetwork>::parse("*").is_err());
        assert!(RecordType::<CurrentNetwork>::parse("**").is_err());
        assert!(RecordType::<CurrentNetwork>::parse("***").is_err());

        // Must not start with a number.
        assert!(RecordType::<CurrentNetwork>::parse("1").is_err());
        assert!(RecordType::<CurrentNetwork>::parse("2").is_err());
        assert!(RecordType::<CurrentNetwork>::parse("3").is_err());
        assert!(RecordType::<CurrentNetwork>::parse("1foo").is_err());
        assert!(RecordType::<CurrentNetwork>::parse("12").is_err());
        assert!(RecordType::<CurrentNetwork>::parse("111").is_err());

        // Must fit within the data capacity of a base field element.
        let record =
            RecordType::<CurrentNetwork>::parse("foo_bar_baz_qux_quux_quuz_corge_grault_garply_waldo_fred_plugh_xyzzy");
        assert!(record.is_err());
    }

    #[test]
    fn test_display() {
        let expected = "record message:\n    owner as address.private;\n    gates as u64.public;\n    first as field.private;\n    second as field.constant;";
        let message = RecordType::<CurrentNetwork>::parse(expected).unwrap().1;
        assert_eq!(expected, format!("{}", message));
    }

    #[test]
    fn test_display_fails() {
        // Duplicate identifier.
        let candidate = RecordType::<CurrentNetwork>::from_str(
            "record message:\n    owner as address.private;\n    gates as u64.public;\n    first as field.public;\n    first as field.constant;",
        );
        assert!(candidate.is_err());

        // Visibility is missing in entry.
        let candidate = RecordType::<CurrentNetwork>::from_str(
            "record message:\n    owner as address.private;\n    gates as u64.public;\n    first as field;\n    first as field.private;",
        );
        assert!(candidate.is_err());

        // Attempted to store another record inside.
        let candidate = RecordType::<CurrentNetwork>::from_str(
            "record message:\n    owner as address.private;\n    gates as u64.public;\n    first as token.record;",
        );
        assert!(candidate.is_err());
    }
}
