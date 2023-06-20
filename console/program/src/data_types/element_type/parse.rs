// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

impl<N: Network> Parser for ElementType<N> {
    /// Parses a string into an element type.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse to determine the element type (order matters).
        alt((
            map(LiteralType::parse, |type_| Self::Literal(type_)),
            map(Identifier::parse, |identifier| Self::Struct(identifier)),
        ))(string)
    }
}

impl<N: Network> FromStr for ElementType<N> {
    type Err = Error;

    /// Returns an element type from a string literal.
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

impl<N: Network> Debug for ElementType<N> {
    /// Prints the element type as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for ElementType<N> {
    /// Prints the element type as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            // Prints the literal, i.e. field
            Self::Literal(literal) => Display::fmt(literal, f),
            // Prints the struct, i.e. signature
            Self::Struct(struct_) => Display::fmt(struct_, f),
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
        assert_eq!(ElementType::parse("field"), Ok(("", ElementType::<CurrentNetwork>::Literal(LiteralType::Field))));
        assert_eq!(
            ElementType::parse("signature"),
            Ok(("", ElementType::<CurrentNetwork>::Struct(Identifier::from_str("signature")?)))
        );
        Ok(())
    }

    #[test]
    fn test_parse_fails() -> Result<()> {
        // Literal type must not contain visibility.
        assert_eq!(
            Ok((".constant", ElementType::<CurrentNetwork>::from_str("field")?)),
            ElementType::<CurrentNetwork>::parse("field.constant")
        );
        assert_eq!(
            Ok((".public", ElementType::<CurrentNetwork>::from_str("field")?)),
            ElementType::<CurrentNetwork>::parse("field.public")
        );
        assert_eq!(
            Ok((".private", ElementType::<CurrentNetwork>::from_str("field")?)),
            ElementType::<CurrentNetwork>::parse("field.private")
        );

        // Struct type must not contain visibility.
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
        assert!(ElementType::<CurrentNetwork>::parse("").is_err());
        assert!(ElementType::<CurrentNetwork>::parse("{}").is_err());

        // Invalid characters.
        assert!(ElementType::<CurrentNetwork>::parse("_").is_err());
        assert!(ElementType::<CurrentNetwork>::parse("__").is_err());
        assert!(ElementType::<CurrentNetwork>::parse("___").is_err());
        assert!(ElementType::<CurrentNetwork>::parse("-").is_err());
        assert!(ElementType::<CurrentNetwork>::parse("--").is_err());
        assert!(ElementType::<CurrentNetwork>::parse("---").is_err());
        assert!(ElementType::<CurrentNetwork>::parse("*").is_err());
        assert!(ElementType::<CurrentNetwork>::parse("**").is_err());
        assert!(ElementType::<CurrentNetwork>::parse("***").is_err());

        // Must not start with a number.
        assert!(ElementType::<CurrentNetwork>::parse("1").is_err());
        assert!(ElementType::<CurrentNetwork>::parse("2").is_err());
        assert!(ElementType::<CurrentNetwork>::parse("3").is_err());
        assert!(ElementType::<CurrentNetwork>::parse("1foo").is_err());
        assert!(ElementType::<CurrentNetwork>::parse("12").is_err());
        assert!(ElementType::<CurrentNetwork>::parse("111").is_err());

        // Must fit within the data capacity of a base field element.
        let struct_ = ElementType::<CurrentNetwork>::parse(
            "foo_bar_baz_qux_quux_quuz_corge_grault_garply_waldo_fred_plugh_xyzzy",
        );
        assert!(struct_.is_err());

        Ok(())
    }

    #[test]
    fn test_display() -> Result<()> {
        assert_eq!(ElementType::<CurrentNetwork>::Literal(LiteralType::Field).to_string(), "field");
        assert_eq!(ElementType::<CurrentNetwork>::Struct(Identifier::from_str("signature")?).to_string(), "signature");
        Ok(())
    }
}
