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

impl<N: Network> Identifier<N> {
    /// Returns the number of bits of this identifier.
    pub fn size_in_bits(&self) -> u8 {
        8 * self.0.len() as u8
    }
}

impl<N: Network> FromBits for Identifier<N> {
    /// Initializes a new identifier from a list of little-endian bits *without* trailing zeros.
    fn from_bits_le(bits_le: &[bool]) -> Result<Self> {
        Self::from_str(&String::from_utf8(Vec::<u8>::from_bits_le(bits_le)?)?)
    }

    /// Initializes a new identifier from a list of big-endian bits *without* leading zeros.
    fn from_bits_be(bits_be: &[bool]) -> Result<Self> {
        Self::from_str(&String::from_utf8(Vec::<u8>::from_bits_be(bits_be)?)?)
    }
}

impl<N: Network> ToBits for Identifier<N> {
    /// Returns the little-endian bits of the identifier.
    fn to_bits_le(&self) -> Vec<bool> {
        (&self).to_bits_le()
    }

    /// Returns the big-endian bits of the identifier.
    fn to_bits_be(&self) -> Vec<bool> {
        (&self).to_bits_be()
    }
}

impl<N: Network> ToBits for &Identifier<N> {
    /// Returns the little-endian bits of the identifier.
    fn to_bits_le(&self) -> Vec<bool> {
        self.0.to_bits_le()
    }

    /// Returns the big-endian bits of the identifier.
    fn to_bits_be(&self) -> Vec<bool> {
        self.0.to_bits_be()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Testnet3;
    use snarkvm_utilities::{test_rng, Rng};

    use rand::distributions::Alphanumeric;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: usize = 100;

    #[test]
    fn test_identifier_bits() -> Result<()> {
        let rng = &mut test_rng();

        for _ in 0..ITERATIONS {
            // Sample a random fixed-length alphanumeric string, that always starts with an alphabetic character.
            let string = "a".to_string()
                + &rng
                    .sample_iter(&Alphanumeric)
                    .take(<CurrentNetwork as Network>::Field::size_in_data_bits() / (8 * 2))
                    .map(char::from)
                    .collect::<String>();

            let identifier = Identifier::<CurrentNetwork>::from_str(&string)?;
            assert_eq!(identifier, Identifier::from_bits_le(&identifier.to_bits_le())?);
            assert_eq!(identifier, Identifier::from_bits_be(&identifier.to_bits_be())?);
        }
        Ok(())
    }
}
