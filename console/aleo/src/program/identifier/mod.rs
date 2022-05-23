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

mod bits;

use crate::Network;
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{
    error,
    io::{Read, Result as IoResult, Write},
    FromBits,
    FromBytes,
    ToBits,
    ToBytes,
};

use anyhow::{bail, Error, Result};
use core::{fmt, marker::PhantomData, str::FromStr};

/// An identifier is an **immutable** UTF-8 string,
/// represented as a **constant** field element in the CurrentNetwork.
///
/// # Requirements
/// The identifier must not be an empty string.
/// The identifier must not start with a number.
/// The identifier must be alphanumeric, and may include underscores.
/// The identifier must not consist solely of underscores.
/// The identifier must fit within the data capacity of a base field element.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Identifier<N: Network>(String, PhantomData<N>);

impl<N: Network> FromStr for Identifier<N> {
    type Err = Error;

    /// Reads in an identifier from a string.
    fn from_str(identifier: &str) -> Result<Self, Self::Err> {
        // Ensure the identifier is not an empty string, and does not start with a number.
        match identifier.chars().next() {
            Some(character) => {
                if character.is_numeric() {
                    bail!("Identifier cannot start with a number")
                }
            }
            None => bail!("Identifier cannot be an empty string"),
        }

        // Ensure the identifier is alphanumeric and underscores.
        if !identifier.chars().all(|character| character.is_alphanumeric() || character == '_') {
            bail!("Identifier must be alphanumeric and underscores")
        }

        // Ensure the identifier is not solely underscores.
        if identifier.chars().all(|character| character == '_') {
            bail!("Identifier cannot consist solely of underscores")
        }

        // Ensure identifier fits within the data capacity of the base field.
        let max_bytes = N::Field::size_in_data_bits() / 8; // Note: This intentionally rounds down.
        if identifier.len() > max_bytes {
            bail!("Identifier is too large. Identifiers must be <= {max_bytes} bytes long")
        }

        // Return the identifier.
        Ok(Self(identifier.to_string(), PhantomData))
    }
}

impl<N: Network> fmt::Display for Identifier<N> {
    /// Prints the identifier as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<N: Network> FromBytes for Identifier<N> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the number of bytes.
        let size = u8::read_le(&mut reader)?;
        // Read the identifier bytes.
        let mut buffer = vec![0u8; size as usize];
        reader.read_exact(&mut buffer)?;
        // from_str the identifier.
        Ok(Self::from_str(
            &String::from_utf8(buffer).map_err(|e| error(format!("Failed to deserialize identifier: {e}")))?,
        )
        .map_err(|e| error(format!("{e}")))?)
    }
}

impl<N: Network> ToBytes for Identifier<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure identifier fits within the data capacity of the base field.
        let max_bytes = N::Field::size_in_data_bits() / 8; // Note: This intentionally rounds down.
        if self.0.as_bytes().len() > max_bytes {
            return Err(error(format!("Identifier is too large. Identifiers must be <= {max_bytes} bytes long")));
        }

        (self.0.as_bytes().len() as u8).write_le(&mut writer)?;
        self.0.as_bytes().write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_identifier_from_str() {
        let candidate = Identifier::<CurrentNetwork>::from_str("foo_bar").unwrap();
        assert_eq!("foo_bar", candidate.0);
    }

    #[test]
    fn test_identifier_from_str_fails() {
        // Must be alphanumeric or underscore.
        assert!(Identifier::<CurrentNetwork>::from_str("foo_bar~baz").is_err());
        assert!(Identifier::<CurrentNetwork>::from_str("foo_bar-baz").is_err());

        // Must not be solely underscores.
        assert!(Identifier::<CurrentNetwork>::from_str("_").is_err());
        assert!(Identifier::<CurrentNetwork>::from_str("__").is_err());
        assert!(Identifier::<CurrentNetwork>::from_str("___").is_err());
        assert!(Identifier::<CurrentNetwork>::from_str("____").is_err());

        // Must not start with a number.
        assert!(Identifier::<CurrentNetwork>::from_str("1").is_err());
        assert!(Identifier::<CurrentNetwork>::from_str("2").is_err());
        assert!(Identifier::<CurrentNetwork>::from_str("3").is_err());
        assert!(Identifier::<CurrentNetwork>::from_str("1foo").is_err());
        assert!(Identifier::<CurrentNetwork>::from_str("12").is_err());
        assert!(Identifier::<CurrentNetwork>::from_str("111").is_err());

        // Must fit within the data capacity of a base field element.
        let identifier = Identifier::<CurrentNetwork>::from_str(
            "foo_bar_baz_qux_quux_quuz_corge_grault_garply_waldo_fred_plugh_xyzzy",
        );
        assert!(identifier.is_err());
    }

    #[test]
    fn test_identifier_display() -> Result<()> {
        let identifier = Identifier::<CurrentNetwork>::from_str("foo_bar")?;
        assert_eq!("foo_bar", format!("{identifier}"));
        Ok(())
    }
}
