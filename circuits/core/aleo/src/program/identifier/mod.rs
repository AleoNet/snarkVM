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

mod from_bits;
mod size_in_bits;
mod to_bits;
mod to_field;

use crate::Aleo;
use snarkvm_circuits_types::{environment::prelude::*, Boolean, Field, U8};
use snarkvm_utilities::{error, FromBits as FB, ToBits as TB};

use nom::character::complete::{alpha1, alphanumeric1};

/// An identifier is an **immutable** UTF-8 string,
/// represented as a **constant** field element in the circuit.
///
/// # Requirements
/// The identifier must not be an empty string.
/// The identifier must not start with a number.
/// The identifier must be alphanumeric, and may include underscores.
/// The identifier must not consist solely of underscores.
/// The identifier must fit within the data capacity of a base field element.
#[derive(Clone)]
pub struct Identifier<A: Aleo>(Field<A>, u8); // Number of bytes

impl<A: Aleo> Inject for Identifier<A> {
    type Primitive = snarkvm_console_aleo::Identifier<A::Network>;

    /// Initializes a new identifier from a string.
    fn new(_: Mode, identifier: Self::Primitive) -> Self {
        // Convert the identifier to a string to check its validity.
        let identifier = identifier.to_string();

        // Ensure the identifier is not an empty string, and does not start with a number.
        match identifier.chars().next() {
            Some(character) => {
                if character.is_numeric() {
                    A::halt(format!("Identifier cannot start with a number"))
                }
            }
            None => A::halt(format!("Identifier cannot be an empty string")),
        }

        // Ensure the identifier is alphanumeric and underscores.
        if !identifier.chars().all(|character| character.is_alphanumeric() || character == '_') {
            A::halt(format!("Identifier must be alphanumeric and underscores"))
        }

        // Ensure the identifier is not solely underscores.
        if identifier.chars().all(|character| character == '_') {
            A::halt(format!("Identifier cannot consist solely of underscores"))
        }

        // Ensure identifier fits within the data capacity of the base field.
        let max_bytes = A::BaseField::size_in_data_bits() / 8; // Note: This intentionally rounds down.
        if identifier.len() > max_bytes {
            A::halt(format!("Identifier is too large. Identifiers must be <= {max_bytes} bytes long"))
        }

        // Note: The string bytes themselves are **not** little-endian. Rather, they are order-preserving
        // for reconstructing the string when recovering the field element back into bytes.
        let field = Field::from_bits_le(&Vec::<Boolean<_>>::constant(identifier.as_bytes().to_bits_le()));

        // Return the identifier.
        Self(field, identifier.as_bytes().len() as u8)
    }
}

impl<A: Aleo> Eject for Identifier<A> {
    type Primitive = snarkvm_console_aleo::Identifier<A::Network>;

    /// Ejects the mode of the identifier.
    fn eject_mode(&self) -> Mode {
        self.0.eject_mode()
    }

    /// Ejects the identifier as a string.
    fn eject_value(&self) -> Self::Primitive {
        // Convert the identifier to bits.
        let bits_le = self.0.to_bits_le().eject_value();
        // Convert the bits to bytes, and parse the bytes as a UTF-8 string.
        match String::from_utf8(
            bits_le
                .chunks(8)
                .map(|byte| match u8::from_bits_le(byte) {
                    Ok(byte) => byte,
                    Err(error) => A::halt(format!("Failed to recover an identifier from bits: {error}")),
                })
                .collect::<Vec<_>>(),
        ) {
            // Truncate the UTF-8 string at the first instance of '\0'.
            Ok(string) => match string.split('\0').next() {
                // Check that the UTF-8 string matches the expected length.
                Some(string) => match string.len() == self.1 as usize {
                    // Return the string.
                    true => match Self::Primitive::try_from(string) {
                        Ok(identifier) => identifier,
                        Err(error) => A::halt(format!("Failed to convert an identifier to a string: {error}")),
                    },
                    false => A::halt(format!("Identifier should be {} bytes, found {} bytes", self.1, string.len())),
                },
                None => A::halt(format!("Identifier exceeds the maximum capacity allowed")),
            },
            Err(error) => A::halt(format!("Failed to eject identifier as string: {error}")),
        }
    }
}

impl<A: Aleo> Parser for Identifier<A> {
    type Environment = A;

    /// Parses a UTF-8 string into an identifier.
    ///
    /// # Requirements
    /// The identifier must not be an empty string.
    /// The identifier must not start with a number.
    /// The identifier must be alphanumeric, and may include underscores.
    /// The identifier must not consist solely of underscores.
    /// The identifier must fit within the data capacity of a base field element.
    /// The identifier must not be a keyword.
    /// The identifier must not be a register format.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Ensure the identifier is not empty, is alphanumeric and underscores, and does not begin with a number.
        map_res(recognize(pair(alt((alpha1, tag("_"))), many0(alt((alphanumeric1, tag("_")))))), |identifier: &str| {
            // Ensure the identifier is not solely underscores.
            if identifier.chars().all(|character| character == '_') {
                return Err(error(format!("Identifier cannot consist solely of underscores")));
            }

            // Ensure identifier fits within the data capacity of the base field.
            let max_bytes = A::BaseField::size_in_data_bits() / 8; // Note: This intentionally rounds down.
            if identifier.as_bytes().len() > max_bytes {
                return Err(error(format!("Identifier is too large. Identifiers must be <= {max_bytes} bytes long")));
            }

            Ok(Self::constant(
                snarkvm_console_aleo::Identifier::try_from(identifier).map_err(|e| error(format!("{e}")))?,
            ))
        })(string)
    }
}

impl<A: Aleo> fmt::Display for Identifier<A> {
    /// Prints the identifier as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.eject_value())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::AleoV0 as Circuit;

    use anyhow::Result;

    #[test]
    fn test_identifier_parse() -> Result<()> {
        let candidate = Identifier::<Circuit>::parse("foo_bar").unwrap();
        assert_eq!("", candidate.0);
        assert_eq!(Identifier::<Circuit>::constant("foo_bar".try_into()?).eject(), candidate.1.eject());
        Ok(())
    }

    #[test]
    fn test_identifier_parse_fails() {
        // Must be alphanumeric or underscore.
        let identifier = Identifier::<Circuit>::parse("foo_bar~baz").unwrap();
        assert_eq!(("~baz", Identifier::<Circuit>::from_str("foo_bar").eject()), (identifier.0, identifier.1.eject()));
        let identifier = Identifier::<Circuit>::parse("foo_bar-baz").unwrap();
        assert_eq!(("-baz", Identifier::<Circuit>::from_str("foo_bar").eject()), (identifier.0, identifier.1.eject()));

        // Must not be solely underscores.
        assert!(Identifier::<Circuit>::parse("_").is_err());
        assert!(Identifier::<Circuit>::parse("__").is_err());
        assert!(Identifier::<Circuit>::parse("___").is_err());
        assert!(Identifier::<Circuit>::parse("____").is_err());

        // Must not start with a number.
        assert!(Identifier::<Circuit>::parse("1").is_err());
        assert!(Identifier::<Circuit>::parse("2").is_err());
        assert!(Identifier::<Circuit>::parse("3").is_err());
        assert!(Identifier::<Circuit>::parse("1foo").is_err());
        assert!(Identifier::<Circuit>::parse("12").is_err());
        assert!(Identifier::<Circuit>::parse("111").is_err());

        // Must fit within the data capacity of a base field element.
        let identifier =
            Identifier::<Circuit>::parse("foo_bar_baz_qux_quux_quuz_corge_grault_garply_waldo_fred_plugh_xyzzy");
        assert!(identifier.is_err());
    }

    #[test]
    fn test_identifier_display() {
        let identifier = Identifier::<Circuit>::from_str("foo_bar");
        assert_eq!("foo_bar", format!("{identifier}"));
    }

    #[test]
    fn test_identifier_bits() {
        let identifier = Identifier::<Circuit>::from_str("foo_bar");
        assert_eq!(
            identifier.to_bits_le().eject(),
            Identifier::from_bits_le(&identifier.to_bits_le()).to_bits_le().eject()
        );
        assert_eq!(
            identifier.to_bits_be().eject(),
            Identifier::from_bits_be(&identifier.to_bits_be()).to_bits_be().eject()
        );
    }
}
