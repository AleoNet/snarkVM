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

impl<N: Network> Parser for FinalizeType<N> {
    /// Parses the string into a finalize type.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the mode from the string.
        alt((
            map(pair(PlaintextType::parse, tag(".public")), |(plaintext_type, _)| Self::Public(plaintext_type)),
            map(pair(Identifier::parse, tag(".record")), |(identifier, _)| Self::Record(identifier)),
            map(pair(Locator::parse, tag(".record")), |(locator, _)| Self::ExternalRecord(locator)),
        ))(string)
    }
}

impl<N: Network> FromStr for FinalizeType<N> {
    type Err = Error;

    /// Returns the finalize type from a string literal.
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

impl<N: Network> Debug for FinalizeType<N> {
    /// Prints the finalize type as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for FinalizeType<N> {
    /// Prints the finalize type as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Public(plaintext_type) => write!(f, "{plaintext_type}.public"),
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
            Ok(("", FinalizeType::<CurrentNetwork>::from_str("field.public")?)),
            FinalizeType::<CurrentNetwork>::parse("field.public")
        );

        // Struct type.
        assert_eq!(
            Ok(("", FinalizeType::<CurrentNetwork>::from_str("signature.public")?)),
            FinalizeType::<CurrentNetwork>::parse("signature.public")
        );

        // Record type.
        assert_eq!(
            Ok(("", FinalizeType::<CurrentNetwork>::from_str("token.record")?)),
            FinalizeType::<CurrentNetwork>::parse("token.record")
        );
        assert_eq!(
            FinalizeType::<CurrentNetwork>::Record(Identifier::from_str("message")?),
            FinalizeType::<CurrentNetwork>::parse("message.record")?.1
        );

        // ExternalRecord type.
        assert_eq!(
            Ok(("", FinalizeType::<CurrentNetwork>::from_str("howard.aleo/message.record")?)),
            FinalizeType::<CurrentNetwork>::parse("howard.aleo/message.record")
        );
        assert_eq!(
            FinalizeType::<CurrentNetwork>::ExternalRecord(Locator::from_str("howard.aleo/message")?),
            FinalizeType::<CurrentNetwork>::parse("howard.aleo/message.record")?.1
        );

        Ok(())
    }

    #[test]
    fn test_parse_fails() -> Result<()> {
        // Literal type must contain visibility.
        assert!(FinalizeType::<CurrentNetwork>::parse("field").is_err());
        // Struct type must contain visibility.
        assert!(FinalizeType::<CurrentNetwork>::parse("signature").is_err());
        // Record type must contain record keyword.
        assert!(FinalizeType::<CurrentNetwork>::parse("token").is_err());

        // Must be non-empty.
        assert!(FinalizeType::<CurrentNetwork>::parse("").is_err());

        // Invalid characters.
        assert!(FinalizeType::<CurrentNetwork>::parse("{}").is_err());
        assert!(FinalizeType::<CurrentNetwork>::parse("_").is_err());
        assert!(FinalizeType::<CurrentNetwork>::parse("__").is_err());
        assert!(FinalizeType::<CurrentNetwork>::parse("___").is_err());
        assert!(FinalizeType::<CurrentNetwork>::parse("-").is_err());
        assert!(FinalizeType::<CurrentNetwork>::parse("--").is_err());
        assert!(FinalizeType::<CurrentNetwork>::parse("---").is_err());
        assert!(FinalizeType::<CurrentNetwork>::parse("*").is_err());
        assert!(FinalizeType::<CurrentNetwork>::parse("**").is_err());
        assert!(FinalizeType::<CurrentNetwork>::parse("***").is_err());

        // Must not start with a number.
        assert!(FinalizeType::<CurrentNetwork>::parse("1").is_err());
        assert!(FinalizeType::<CurrentNetwork>::parse("2").is_err());
        assert!(FinalizeType::<CurrentNetwork>::parse("3").is_err());
        assert!(FinalizeType::<CurrentNetwork>::parse("1foo").is_err());
        assert!(FinalizeType::<CurrentNetwork>::parse("12").is_err());
        assert!(FinalizeType::<CurrentNetwork>::parse("111").is_err());

        // Must fit within the data capacity of a base field element.
        let struct_ = FinalizeType::<CurrentNetwork>::parse(
            "foo_bar_baz_qux_quux_quuz_corge_grault_garply_waldo_fred_plugh_xyzzy.private",
        );
        assert!(struct_.is_err());

        Ok(())
    }

    #[test]
    fn test_display() -> Result<()> {
        assert_eq!(FinalizeType::<CurrentNetwork>::from_str("field.public")?.to_string(), "field.public");

        assert_eq!(FinalizeType::<CurrentNetwork>::from_str("signature.public")?.to_string(), "signature.public");

        assert_eq!(FinalizeType::<CurrentNetwork>::from_str("token.record")?.to_string(), "token.record");

        assert_eq!(
            FinalizeType::<CurrentNetwork>::from_str("howard.aleo/message.record")?.to_string(),
            "howard.aleo/message.record"
        );

        Ok(())
    }
}
