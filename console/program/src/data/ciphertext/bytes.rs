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

impl<N: Network> FromBytes for Ciphertext<N> {
    /// Reads the ciphertext from a buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the number of field elements.
        let num_fields = u16::read_le(&mut reader)?;
        // Ensure the number of field elements does not exceed the maximum allowed size.
        match num_fields as u32 <= N::MAX_DATA_SIZE_IN_FIELDS {
            // Read the field elements.
            true => {
                Ok(Ciphertext((0..num_fields).map(|_| Field::read_le(&mut reader)).collect::<Result<Vec<_>, _>>()?))
            }
            false => Err(error("Ciphertext is too large to encode in field elements.")),
        }
    }
}

impl<N: Network> ToBytes for Ciphertext<N> {
    /// Writes the ciphertext to a buffer.
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of field elements does not exceed the maximum allowed size.
        if self.0.len() as u32 > N::MAX_DATA_SIZE_IN_FIELDS {
            return Err(error("Ciphertext is too large to encode in field elements."));
        }
        // Write the number of ciphertext field elements.
        (self.0.len() as u16).write_le(&mut writer)?;
        // Write the ciphertext field elements.
        self.0.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u32 = 1000;

    #[test]
    fn test_bytes() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new ciphertext.
            let expected =
                Ciphertext::<CurrentNetwork>((0..100).map(|_| Uniform::rand(&mut test_rng())).collect::<Vec<_>>());

            // Check the byte representation.
            let expected_bytes = expected.to_bytes_le()?;
            assert_eq!(expected, Ciphertext::read_le(&expected_bytes[..])?);
            // assert!(Ciphertext::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());
        }
        Ok(())
    }
}
