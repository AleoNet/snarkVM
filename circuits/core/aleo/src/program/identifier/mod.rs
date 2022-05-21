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

use crate::Aleo;
use snarkvm_circuits_types::{environment::prelude::*, Boolean, Field};
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
pub struct Identifier<A: Aleo>(Field<A>, u8);

impl<A: Aleo> Inject for Identifier<A> {
    type Primitive = String;

    /// Initializes a new identifier from a string.
    fn new(_: Mode, identifier: Self::Primitive) -> Self {
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
        if identifier.as_bytes().len() > max_bytes {
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
    type Primitive = String;

    /// Ejects the mode of the identifier.
    fn eject_mode(&self) -> Mode {
        self.0.eject_mode()
    }

    /// Ejects the identifier as a string.
    fn eject_value(&self) -> Self::Primitive {
        // Convert the identifier to bits.
        let bits_le = self.0.to_bits_le().eject_value();
        // Convert the bits to bytes, and parse the bytes as a UTF-8 string.
        match String::from_utf8(bits_le.chunks(8).map(u8::from_bits_le).collect()) {
            // Truncate the UTF-8 string at the first instance of '\0'.
            Ok(string) => match string.split('\0').next() {
                // Check that the UTF-8 string matches the expected length.
                Some(string) => match string.len() == self.1 as usize {
                    // Return the string.
                    true => string.to_string(),
                    false => A::halt(format!("Identifier should be {} bytes, found {} bytes", self.1, string.len())),
                },
                None => A::halt(format!("Identifier exceeds the maximum capacity allowed")),
            },
            Err(error) => A::halt(format!("Failed to eject identifier as string: {error}")),
        }
    }
}

impl<A: Aleo> FromBits for Identifier<A> {
    type Boolean = Boolean<A>;

    /// Initializes a new identifier from little-endian bits.
    fn from_bits_le(bits_le: &[Self::Boolean]) -> Self {
        // Recover the field element from the bits.
        let field = Field::from_bits_le(bits_le);
        // Recover the identifier length from the bits.
        let num_bytes = {
            // Eject the bits in **little-endian** form.
            let bits_le = field.to_bits_le().eject_value();
            // Convert the bits to bytes, and parse the bytes as a UTF-8 string.
            let bytes = bits_le.chunks(8).map(u8::from_bits_le).collect::<Vec<_>>();
            // Find the first instance of a `0` byte, which is the null character '\0' in UTF-8,
            // and an invalid character according to our rules for representing an identifier.
            match bytes.iter().position(|&byte| byte == 0) {
                Some(index) => index,
                None => A::halt(format!("Identifier exceeds the maximum capacity allowed")),
            }
        };
        // Ensure identifier fits within the data capacity of the base field.
        let max_bytes = A::BaseField::size_in_data_bits() / 8; // Note: This intentionally rounds down.
        match num_bytes <= max_bytes {
            // Return the identifier.
            true => Self(field, num_bytes as u8),
            false => A::halt(format!("Identifier exceeds the maximum capacity allowed")),
        }
    }

    /// Initializes a new identifier from big-endian bits.
    fn from_bits_be(bits_be: &[Self::Boolean]) -> Self {
        // Recover the field element from the bits.
        let field = Field::from_bits_be(bits_be);
        // Recover the identifier length from the bits.
        let num_bytes = {
            // Eject the bits in **little-endian** form (this is correct for this `from_bits_be` case).
            let bits_le = field.to_bits_le().eject_value();
            // Convert the bits to bytes, and parse the bytes as a UTF-8 string.
            let bytes = bits_le.chunks(8).map(u8::from_bits_le).collect::<Vec<_>>();
            // Find the first instance of a `0` byte, which is the null character '\0' in UTF-8,
            // and an invalid character according to our rules for representing an identifier.
            match bytes.iter().position(|&byte| byte == 0) {
                Some(index) => index,
                None => A::halt(format!("Identifier exceeds the maximum capacity allowed")),
            }
        };
        // Ensure identifier fits within the data capacity of the base field.
        let max_bytes = A::BaseField::size_in_data_bits() / 8; // Note: This intentionally rounds down.
        match num_bytes <= max_bytes {
            // Return the identifier.
            true => Self(field, num_bytes as u8),
            false => A::halt(format!("Identifier exceeds the maximum capacity allowed")),
        }
    }
}

impl<A: Aleo> ToBits for Identifier<A> {
    type Boolean = Boolean<A>;

    /// Returns the little-endian bits of the identifier.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        self.0.to_bits_le()[..self.1 as usize].to_vec()
    }

    /// Returns the big-endian bits of the identifier.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        self.0.to_bits_be()[..self.1 as usize].to_vec()
    }
}

impl<A: Aleo> ToField for Identifier<A> {
    type Field = Field<A>;

    /// Returns the identifier as a base field element.
    fn to_field(&self) -> Self::Field {
        self.0.clone()
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

            Ok(Self::constant(identifier.to_string()))
        })(string)
    }
}

impl<A: Aleo> fmt::Display for Identifier<A> {
    /// Prints the identifier as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.eject_value())
    }
}

// impl<A: Aleo> FromBytes for Identifier<A> {
//     fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
//         // Read the number of bytes.
//         let size = u8::read_le(&mut reader)?;
//         // Read the identifier bytes.
//         let mut buffer = vec![0u8; size as usize];
//         reader.read_exact(&mut buffer)?;
//         // Parse the identifier.
//         Ok(Self::from_str(
//             &String::from_utf8(buffer).map_err(|e| error(format!("Failed to deserialize identifier: {e}")))?,
//         ))
//     }
// }
//
// impl<A: Aleo> ToBytes for Identifier<A> {
//     fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
//         // Ensure identifier is less than or equal to `NUM_IDENTIFIER_BYTES` bytes long.
//         if self.0.as_bytes().len() > P::NUM_IDENTIFIER_BYTES {
//             return Err(error(format!(
//                 "Identifier is too large. Identifiers must be <= {} bytes long",
//                 P::NUM_IDENTIFIER_BYTES
//             )));
//         }
//
//         (self.0.as_bytes().len() as u8).write_le(&mut writer)?;
//         self.0.as_bytes().write_le(&mut writer)
//     }
// }

#[cfg(test)]
mod tests {
    use super::*;
    use crate::AleoV0 as Circuit;

    #[test]
    fn test_identifier_parse() {
        let candidate = Identifier::<Circuit>::parse("foo_bar").unwrap();
        assert_eq!("", candidate.0);
        assert_eq!(Identifier::<Circuit>::constant("foo_bar".to_string()).eject(), candidate.1.eject());
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
}
