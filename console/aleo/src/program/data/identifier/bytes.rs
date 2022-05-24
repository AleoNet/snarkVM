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

impl<N: Network> FromBytes for Identifier<N> {
    /// Reads in an identifier from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the number of bytes.
        let size = u8::read_le(&mut reader)?;
        // Read the identifier bytes.
        let mut buffer = vec![0u8; size as usize];
        reader.read_exact(&mut buffer)?;
        // from_str the identifier.
        Self::from_str(&String::from_utf8(buffer).map_err(|e| error(format!("Failed to deserialize identifier: {e}")))?)
            .map_err(|e| error(format!("{e}")))
    }
}

impl<N: Network> ToBytes for Identifier<N> {
    /// Writes an identifier to a buffer.
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
    use snarkvm_utilities::{test_rng, Rng};

    use anyhow::Result;
    use rand::distributions::Alphanumeric;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 1000;

    #[test]
    fn test_bytes() -> Result<()> {
        let rng = &mut test_rng();

        for _ in 0..ITERATIONS {
            // Sample a random fixed-length alphanumeric string, that always starts with an alphabetic character.
            let string = "a".to_string()
                + &rng
                    .sample_iter(&Alphanumeric)
                    .take(<CurrentNetwork as Network>::Field::size_in_data_bits() / (8 * 2))
                    .map(char::from)
                    .collect::<String>();
            let expected = Identifier::<CurrentNetwork>::from_str(&string)?;

            // Check the byte representation.
            let expected_bytes = expected.to_bytes_le()?;
            assert_eq!(expected, Identifier::read_le(&expected_bytes[..])?);
            assert!(Identifier::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());
        }
        Ok(())
    }
}
