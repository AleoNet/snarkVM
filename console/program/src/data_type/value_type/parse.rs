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
        // Parse to determine the value type (order matters).
        alt((
            map(LiteralType::parse, |type_| Self::Literal(type_)),
            map(Identifier::parse, |identifier| Self::Interface(identifier)),
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
            // Prints the literal, i.e. field
            Self::Literal(literal) => Display::fmt(literal, f),
            // Prints the interface, i.e. signature
            Self::Interface(interface) => Display::fmt(interface, f),
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
        assert_eq!(ValueType::parse("field"), Ok(("", ValueType::<CurrentNetwork>::Literal(LiteralType::Field))));
        assert_eq!(
            ValueType::parse("signature"),
            Ok(("", ValueType::<CurrentNetwork>::Interface(Identifier::from_str("signature")?)))
        );
        Ok(())
    }

    #[test]
    fn test_parse_fails() -> Result<()> {
        // Literal type must not contain visibility.
        assert_eq!(
            Ok((".constant", ValueType::<CurrentNetwork>::from_str("field")?)),
            ValueType::<CurrentNetwork>::parse("field.constant")
        );
        assert_eq!(
            Ok((".public", ValueType::<CurrentNetwork>::from_str("field")?)),
            ValueType::<CurrentNetwork>::parse("field.public")
        );
        assert_eq!(
            Ok((".private", ValueType::<CurrentNetwork>::from_str("field")?)),
            ValueType::<CurrentNetwork>::parse("field.private")
        );

        // Interface type must not contain visibility.
        assert_eq!(
            Ok((".constant", Identifier::<CurrentNetwork>::from_str("signature")?)),
            Identifier::<CurrentNetwork>::parse("signature.constant")
        );
        assert_eq!(
            Ok((".public", Identifier::<CurrentNetwork>::from_str("signature")?)),
            Identifier::<CurrentNetwork>::parse("signature.public")
        );
        assert_eq!(
            Ok((".private", Identifier::<CurrentNetwork>::from_str("signature")?)),
            Identifier::<CurrentNetwork>::parse("signature.private")
        );

        // Must be non-empty.
        assert!(ValueType::<CurrentNetwork>::parse("").is_err());
        assert!(ValueType::<CurrentNetwork>::parse("{}").is_err());

        // Invalid characters.
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
        let interface =
            ValueType::<CurrentNetwork>::parse("foo_bar_baz_qux_quux_quuz_corge_grault_garply_waldo_fred_plugh_xyzzy");
        assert!(interface.is_err());

        Ok(())
    }

    #[test]
    fn test_display() -> Result<()> {
        assert_eq!(ValueType::<CurrentNetwork>::Literal(LiteralType::Field).to_string(), "field");
        assert_eq!(ValueType::<CurrentNetwork>::Interface(Identifier::from_str("signature")?).to_string(), "signature");
        Ok(())
    }
}
