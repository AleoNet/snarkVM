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

impl<N: Network> Parser for ValueType<N> {
    /// Parses a string into a value type.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the mode from the string.
        alt((
            map(pair(PlaintextType::parse, tag(".constant")), |(plaintext_type, _)| Self::Constant(plaintext_type)),
            map(pair(PlaintextType::parse, tag(".public")), |(plaintext_type, _)| Self::Public(plaintext_type)),
            map(pair(PlaintextType::parse, tag(".private")), |(plaintext_type, _)| Self::Private(plaintext_type)),
            map(pair(Identifier::parse, tag(".record")), |(identifier, _)| Self::Record(identifier)),
            map(pair(Locator::parse, tag(".record")), |(locator, _)| Self::ExternalRecord(locator)),
        ))(string)
    }
}

impl<N: Network> FromStr for ValueType<N> {
    type Err = Error;

    /// Returns a value type from a string literal.
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

impl<N: Network> Debug for ValueType<N> {
    /// Prints the value type as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for ValueType<N> {
    /// Prints the value type as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Constant(plaintext_type) => write!(f, "{plaintext_type}.constant"),
            Self::Public(plaintext_type) => write!(f, "{plaintext_type}.public"),
            Self::Private(plaintext_type) => write!(f, "{plaintext_type}.private"),
            Self::Record(identifier) => write!(f, "{identifier}.record"),
            Self::ExternalRecord(locator) => write!(f, "{locator}.record"),
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
        // Literal type.
        assert_eq!(
            Ok(("", ValueType::<CurrentNetwork>::from_str("field.constant")?)),
            ValueType::<CurrentNetwork>::parse("field.constant")
        );
        assert_eq!(
            Ok(("", ValueType::<CurrentNetwork>::from_str("field.public")?)),
            ValueType::<CurrentNetwork>::parse("field.public")
        );
        assert_eq!(
            Ok(("", ValueType::<CurrentNetwork>::from_str("field.private")?)),
            ValueType::<CurrentNetwork>::parse("field.private")
        );

        // Interface type.
        assert_eq!(
            Ok(("", ValueType::<CurrentNetwork>::from_str("signature.constant")?)),
            ValueType::<CurrentNetwork>::parse("signature.constant")
        );
        assert_eq!(
            Ok(("", ValueType::<CurrentNetwork>::from_str("signature.public")?)),
            ValueType::<CurrentNetwork>::parse("signature.public")
        );
        assert_eq!(
            Ok(("", ValueType::<CurrentNetwork>::from_str("signature.private")?)),
            ValueType::<CurrentNetwork>::parse("signature.private")
        );

        // Record type.
        assert_eq!(
            Ok(("", ValueType::<CurrentNetwork>::from_str("token.record")?)),
            ValueType::<CurrentNetwork>::parse("token.record")
        );

        // ExternalRecord type.
        assert_eq!(
            Ok(("", ValueType::<CurrentNetwork>::from_str("howard.aleo/message.record")?)),
            ValueType::<CurrentNetwork>::parse("howard.aleo/message.record")
        );

        Ok(())
    }

    #[test]
    fn test_parse_fails() -> Result<()> {
        // Literal type must contain visibility.
        assert!(ValueType::<CurrentNetwork>::parse("field").is_err());
        // Interface type must contain visibility.
        assert!(ValueType::<CurrentNetwork>::parse("signature").is_err());
        // Record type must contain record keyword.
        assert!(ValueType::<CurrentNetwork>::parse("token").is_err());

        // Must be non-empty.
        assert!(ValueType::<CurrentNetwork>::parse("").is_err());

        // Invalid characters.
        assert!(ValueType::<CurrentNetwork>::parse("{}").is_err());
        assert!(ValueType::<CurrentNetwork>::parse("_").is_err());
        assert!(ValueType::<CurrentNetwork>::parse("__").is_err());
        assert!(ValueType::<CurrentNetwork>::parse("___").is_err());
        assert!(ValueType::<CurrentNetwork>::parse("-").is_err());
        assert!(ValueType::<CurrentNetwork>::parse("--").is_err());
        assert!(ValueType::<CurrentNetwork>::parse("---").is_err());
        assert!(ValueType::<CurrentNetwork>::parse("*").is_err());
        assert!(ValueType::<CurrentNetwork>::parse("**").is_err());
        assert!(ValueType::<CurrentNetwork>::parse("***").is_err());

        // Must not start with a number.
        assert!(ValueType::<CurrentNetwork>::parse("1").is_err());
        assert!(ValueType::<CurrentNetwork>::parse("2").is_err());
        assert!(ValueType::<CurrentNetwork>::parse("3").is_err());
        assert!(ValueType::<CurrentNetwork>::parse("1foo").is_err());
        assert!(ValueType::<CurrentNetwork>::parse("12").is_err());
        assert!(ValueType::<CurrentNetwork>::parse("111").is_err());

        // Must fit within the data capacity of a base field element.
        let interface = ValueType::<CurrentNetwork>::parse(
            "foo_bar_baz_qux_quux_quuz_corge_grault_garply_waldo_fred_plugh_xyzzy.private",
        );
        assert!(interface.is_err());

        Ok(())
    }

    #[test]
    fn test_display() -> Result<()> {
        assert_eq!(ValueType::<CurrentNetwork>::from_str("field.constant")?.to_string(), "field.constant");
        assert_eq!(ValueType::<CurrentNetwork>::from_str("field.public")?.to_string(), "field.public");
        assert_eq!(ValueType::<CurrentNetwork>::from_str("field.private")?.to_string(), "field.private");

        assert_eq!(ValueType::<CurrentNetwork>::from_str("signature.constant")?.to_string(), "signature.constant");
        assert_eq!(ValueType::<CurrentNetwork>::from_str("signature.public")?.to_string(), "signature.public");
        assert_eq!(ValueType::<CurrentNetwork>::from_str("signature.private")?.to_string(), "signature.private");

        assert_eq!(ValueType::<CurrentNetwork>::from_str("token.record")?.to_string(), "token.record");

        assert_eq!(
            ValueType::<CurrentNetwork>::from_str("howard.aleo/message.record")?.to_string(),
            "howard.aleo/message.record"
        );

        Ok(())
    }
}
