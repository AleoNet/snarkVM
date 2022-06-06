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

impl<N: Network> Parser for Entry<N> {
    /// Parses a string into an entry.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the value type from the string.
        let (string, value_type) = ValueType::parse(string)?;
        // Parse the "." from the string.
        let (string, _) = tag(".")(string)?;
        // Parse the mode from the string.
        let (string, entry) = alt((
            map(tag("constant"), move |_| Self::Constant(value_type)),
            map(tag("public"), move |_| Self::Public(value_type)),
            map(tag("private"), move |_| Self::Private(value_type)),
        ))(string)?;
        // Return the entry.
        Ok((string, entry))
    }
}

impl<N: Network> FromStr for Entry<N> {
    type Err = Error;

    /// Returns an entry from a string literal.
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
    /// Prints the entry as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Entry<N> {
    /// Prints the entry as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Constant(value_type) => write!(f, "{value_type}.constant"),
            Self::Public(value_type) => write!(f, "{value_type}.public"),
            Self::Private(value_type) => write!(f, "{value_type}.private"),
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
            Ok(("", Entry::<CurrentNetwork>::from_str("field.constant")?)),
            Entry::<CurrentNetwork>::parse("field.constant")
        );
        assert_eq!(
            Ok(("", Entry::<CurrentNetwork>::from_str("field.public")?)),
            Entry::<CurrentNetwork>::parse("field.public")
        );
        assert_eq!(
            Ok(("", Entry::<CurrentNetwork>::from_str("field.private")?)),
            Entry::<CurrentNetwork>::parse("field.private")
        );

        // Interface type.
        assert_eq!(
            Ok(("", Entry::<CurrentNetwork>::from_str("signature.constant")?)),
            Entry::<CurrentNetwork>::parse("signature.constant")
        );
        assert_eq!(
            Ok(("", Entry::<CurrentNetwork>::from_str("signature.public")?)),
            Entry::<CurrentNetwork>::parse("signature.public")
        );
        assert_eq!(
            Ok(("", Entry::<CurrentNetwork>::from_str("signature.private")?)),
            Entry::<CurrentNetwork>::parse("signature.private")
        );

        Ok(())
    }

    #[test]
    fn test_parse_fails() -> Result<()> {
        // Literal type must contain visibility.
        assert!(Entry::<CurrentNetwork>::parse("field").is_err());
        // Interface type must contain visibility.
        assert!(Entry::<CurrentNetwork>::parse("signature").is_err());

        // Must be non-empty.
        assert!(Entry::<CurrentNetwork>::parse("").is_err());

        // Invalid characters.
        assert!(Entry::<CurrentNetwork>::parse("{}").is_err());
        assert!(Entry::<CurrentNetwork>::parse("_").is_err());
        assert!(Entry::<CurrentNetwork>::parse("__").is_err());
        assert!(Entry::<CurrentNetwork>::parse("___").is_err());
        assert!(Entry::<CurrentNetwork>::parse("-").is_err());
        assert!(Entry::<CurrentNetwork>::parse("--").is_err());
        assert!(Entry::<CurrentNetwork>::parse("---").is_err());
        assert!(Entry::<CurrentNetwork>::parse("*").is_err());
        assert!(Entry::<CurrentNetwork>::parse("**").is_err());
        assert!(Entry::<CurrentNetwork>::parse("***").is_err());

        // Must not start with a number.
        assert!(Entry::<CurrentNetwork>::parse("1").is_err());
        assert!(Entry::<CurrentNetwork>::parse("2").is_err());
        assert!(Entry::<CurrentNetwork>::parse("3").is_err());
        assert!(Entry::<CurrentNetwork>::parse("1foo").is_err());
        assert!(Entry::<CurrentNetwork>::parse("12").is_err());
        assert!(Entry::<CurrentNetwork>::parse("111").is_err());

        // Must fit within the data capacity of a base field element.
        let interface = Entry::<CurrentNetwork>::parse(
            "foo_bar_baz_qux_quux_quuz_corge_grault_garply_waldo_fred_plugh_xyzzy.private",
        );
        assert!(interface.is_err());

        Ok(())
    }

    #[test]
    fn test_display() -> Result<()> {
        assert_eq!(Entry::<CurrentNetwork>::from_str("field.constant")?.to_string(), "field.constant");
        assert_eq!(Entry::<CurrentNetwork>::from_str("field.public")?.to_string(), "field.public");
        assert_eq!(Entry::<CurrentNetwork>::from_str("field.private")?.to_string(), "field.private");

        assert_eq!(Entry::<CurrentNetwork>::from_str("signature.constant")?.to_string(), "signature.constant");
        assert_eq!(Entry::<CurrentNetwork>::from_str("signature.public")?.to_string(), "signature.public");
        assert_eq!(Entry::<CurrentNetwork>::from_str("signature.private")?.to_string(), "signature.private");

        Ok(())
    }
}
