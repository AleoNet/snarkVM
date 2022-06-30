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

mod bytes;
mod from_bits;
mod from_field;
mod parse;
mod serialize;
mod size_in_bits;
mod to_bits;
mod to_field;

use snarkvm_console_network::Network;
use snarkvm_console_types::{prelude::*, Field};

/// An identifier is an **immutable** UTF-8 string,
/// represented as a **constant** field element in the CurrentNetwork.
///
/// # Requirements
/// The identifier must not be an empty string.
/// The identifier must not start with a number.
/// The identifier must be alphanumeric, and may include underscores.
/// The identifier must not consist solely of underscores.
/// The identifier must fit within the data capacity of a base field element.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Identifier<N: Network>(Field<N>, u8); // Number of bytes in the identifier.

impl<N: Network> TryFrom<&str> for Identifier<N> {
    type Error = Error;

    /// Initializes an identifier from a string.
    fn try_from(identifier: &str) -> Result<Self> {
        Self::from_str(identifier)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: usize = 100;

    /// Samples a random identifier.
    pub(crate) fn sample_identifier<N: Network>() -> Result<Identifier<N>> {
        // Sample a random fixed-length alphanumeric string, that always starts with an alphabetic character.
        let string = sample_identifier_as_string::<N>()?;
        // Recover the field element from the bits.
        let field = Field::<N>::from_bits_le(&string.as_bytes().to_bits_le())?;
        // Return the identifier.
        Ok(Identifier(field, string.len() as u8))
    }

    /// Samples a random identifier as a string.
    pub(crate) fn sample_identifier_as_string<N: Network>() -> Result<String> {
        // Initialize a test RNG.
        let rng = &mut test_rng();
        // Sample a random fixed-length alphanumeric string, that always starts with an alphabetic character.
        let string = "a".to_string()
            + &rng
                .sample_iter(&Alphanumeric)
                .take(Field::<N>::size_in_data_bits() / (8 * 2))
                .map(char::from)
                .collect::<String>();
        // Ensure identifier fits within the data capacity of the base field.
        let max_bytes = Field::<N>::size_in_data_bits() / 8; // Note: This intentionally rounds down.
        match string.len() <= max_bytes {
            // Return the identifier.
            true => Ok(string),
            false => bail!("Identifier exceeds the maximum capacity allowed"),
        }
    }

    #[test]
    fn test_try_from() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a random fixed-length alphanumeric string, that always starts with an alphabetic character.
            let expected_string = sample_identifier_as_string::<CurrentNetwork>()?;
            // Recover the field element from the bits.
            let expected_field = Field::<CurrentNetwork>::from_bits_le(&expected_string.as_bytes().to_bits_le())?;

            // Try to initialize an identifier from the string.
            let candidate = Identifier::<CurrentNetwork>::try_from(expected_string.as_str())?;
            assert_eq!(expected_field, candidate.0);
            assert_eq!(expected_string.len(), candidate.1 as usize);
        }
        Ok(())
    }
}
