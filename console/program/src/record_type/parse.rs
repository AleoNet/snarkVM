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
    ///       balance as u64.public;
    /// ```
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        /// Parses a string into a tuple.
        fn parse_tuple<N: Network>(string: &str) -> ParserResult<(Identifier<N>, ValueType<N>)> {
            // Parse the whitespace and comments from the string.
            let (string, _) = Sanitizer::parse(string)?;
            // Parse the identifier from the string.
            let (string, identifier) = Identifier::parse(string)?;
            // Parse the " as " from the string.
            let (string, _) = tag(" as ")(string)?;
            // Parse the value type from the string.
            let (string, value_type) = ValueType::parse(string)?;
            // Parse the semicolon ';' keyword from the string.
            let (string, _) = tag(";")(string)?;
            // Return the identifier and value type.
            Ok((string, (identifier, value_type)))
        }

        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the type name from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the space from the string.
        let (string, _) = tag(" ")(string)?;
        // Parse the record name from the string.
        let (string, name) = Identifier::parse(string)?;
        // Parse the colon ':' keyword from the string.
        let (string, _) = tag(":")(string)?;
        // Parse the entries from the string.
        let (string, entries) = map_res(many1(parse_tuple), |entries| {
            // Ensure the entries has no duplicate names.
            if has_duplicates(entries.iter().map(|(identifier, _)| identifier)) {
                return Err(error(format!("Duplicate identifier found in record '{}'", name)));
            }
            // Ensure the number of members is within `N::MAX_DATA_ENTRIES`.
            if entries.len() > N::MAX_DATA_ENTRIES {
                return Err(error("Failed to parse record: too many entries"));
            }
            Ok(entries)
        })(string)?;
        // Return the record type.
        Ok((string, Self { name, entries }))
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

#[allow(clippy::format_push_string)]
impl<N: Network> Display for RecordType<N> {
    /// Prints the record type as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let mut output = format!("{} {}:\n", Self::type_name(), self.name);
        for (identifier, value_type) in &self.entries {
            output += &format!("    {identifier} as {value_type};\n");
        }
        output.pop(); // trailing newline
        write!(f, "{}", output)
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
            entries: vec![
                (Identifier::from_str("sender")?, ValueType::from_str("address.private")?),
                (Identifier::from_str("amount")?, ValueType::from_str("u64.public")?),
            ],
        };

        let (remainder, candidate) = RecordType::<CurrentNetwork>::parse(
            r"
record message:
    sender as address.private;
    amount as u64.public;
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
        let expected = "record message:\n    first as field.private;\n    second as field.constant;";
        let message = RecordType::<CurrentNetwork>::parse(expected).unwrap().1;
        assert_eq!(expected, format!("{}", message));
    }

    #[test]
    fn test_display_fails() {
        // Duplicate identifier.
        let candidate = RecordType::<CurrentNetwork>::parse(
            "record message:\n    first as field.public;\n    first as field.constant;",
        );
        assert!(candidate.is_err());
        // Visibility is missing in entry.
        let candidate =
            RecordType::<CurrentNetwork>::parse("record message:\n    first as field;\n    first as field.private;");
        assert!(candidate.is_err());
    }

    // #[test]
    // fn test_matches() {
    //     // Test a struct.
    //     let message =
    //         Definition::<CurrentNetwork>::from_str("record message:\n    first as field.public;\n    second as field.private;");
    //     let message_value = Value::from_str("message { 2field.public, 3field.private }");
    //     let message_value_fails_1 = Value::from_str("message { 2field.public }");
    //     let message_value_fails_2 = Value::from_str("message { 2field.private, 3field.private }");
    //     let message_value_fails_3 = Value::from_str("message { 2field.public, 3field.private, 2field.public }");
    //     assert!(message.matches(&message_value));
    //     assert!(!message.matches(&message_value_fails_1));
    //     assert!(!message.matches(&message_value_fails_2));
    //     assert!(!message.matches(&message_value_fails_3));
    // }
}
