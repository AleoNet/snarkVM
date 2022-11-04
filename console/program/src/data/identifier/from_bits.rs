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

impl<N: Network> FromBits for Identifier<N> {
    /// Initializes a new identifier from a list of little-endian bits *without* trailing zeros.
    fn from_bits_le(bits_le: &[bool]) -> Result<Self> {
        // Ensure the number of bits does not exceed the size in bits of the field.
        // This check is not sufficient to ensure the identifier is of valid size,
        // the final step checks the byte-aligned field element is within the data capacity.
        ensure!(bits_le.len() <= Field::<N>::size_in_bits(), "Identifier exceeds the maximum bits allowed");

        // Convert the bits to bytes, and parse the bytes as a UTF-8 string.
        let bytes = bits_le.chunks(8).map(u8::from_bits_le).collect::<Result<Vec<u8>>>()?;

        // Recover the identifier length from the bits, by finding the first instance of a `0` byte,
        // which is the null character '\0' in UTF-8, and an invalid character in an identifier.
        let num_bytes = match bytes.iter().position(|&byte| byte == 0) {
            Some(index) => index, // `index` is 0-indexed, and we exclude the null character.
            None => bytes.len(),  // No null character found, so the identifier is the full length.
        };

        // Parse the bytes as a UTF-8 string.
        Self::from_str(str::from_utf8(&bytes[0..num_bytes])?)
    }

    /// Initializes a new identifier from a list of big-endian bits *without* leading zeros.
    fn from_bits_be(bits_be: &[bool]) -> Result<Self> {
        Self::from_bits_le(&bits_be.iter().rev().copied().collect::<Vec<bool>>())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::identifier::tests::sample_identifier;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: usize = 100;

    #[test]
    fn test_from_bits_le() -> Result<()> {
        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a random fixed-length alphanumeric identifier, that always starts with an alphabetic character.
            let identifier = sample_identifier::<CurrentNetwork>(&mut rng)?;
            assert_eq!(identifier, Identifier::from_bits_le(&identifier.to_bits_le())?);
        }
        Ok(())
    }

    #[test]
    fn test_from_bits_be() -> Result<()> {
        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a random fixed-length alphanumeric identifier, that always starts with an alphabetic character.
            let identifier = sample_identifier::<CurrentNetwork>(&mut rng)?;
            assert_eq!(identifier, Identifier::from_bits_be(&identifier.to_bits_be())?);
        }
        Ok(())
    }
}
