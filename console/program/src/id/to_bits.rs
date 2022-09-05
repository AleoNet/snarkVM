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

impl<N: Network> ToBits for ProgramID<N> {
    /// Returns the little-endian bits of the program ID.
    fn to_bits_le(&self) -> Vec<bool> {
        (&self).to_bits_le()
    }

    /// Returns the big-endian bits of the program ID.
    fn to_bits_be(&self) -> Vec<bool> {
        (&self).to_bits_be()
    }
}

impl<N: Network> ToBits for &ProgramID<N> {
    /// Returns the little-endian bits of the program ID.
    fn to_bits_le(&self) -> Vec<bool> {
        let mut bits = self.name().to_bits_le();
        bits.extend(self.network().to_bits_le());
        bits
    }

    /// Returns the big-endian bits of the program ID.
    fn to_bits_be(&self) -> Vec<bool> {
        let mut bits = self.name().to_bits_be();
        bits.extend(self.network().to_bits_be());
        bits
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::identifier::tests::sample_identifier_as_string;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: usize = 100;

    #[test]
    fn test_to_bits_le() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a random fixed-length alphanumeric string, that always starts with an alphabetic character.
            let expected_name_string = sample_identifier_as_string::<CurrentNetwork>()?;
            // Recover the field element from the bits.
            let expected_name_field = Field::<CurrentNetwork>::from_bits_le(&expected_name_string.to_bits_le())?;
            let expected_network_field = Field::<CurrentNetwork>::from_bits_le(&"aleo".to_string().to_bits_le())?;
            // Compute the expected bits.
            let mut expected_bits = expected_name_field.to_bits_le()[..expected_name_string.len() * 8].to_vec();
            expected_bits.extend(&expected_network_field.to_bits_le()[..4 * 8]);

            let candidate = ProgramID::<CurrentNetwork>::from_str(&format!("{expected_name_string}.aleo"))?;
            assert_eq!(
                expected_name_field.to_bits_le()[..expected_name_string.len() * 8],
                candidate.name().to_bits_le()
            );
            assert_eq!(expected_network_field.to_bits_le()[..4 * 8], candidate.network().to_bits_le());
            assert_eq!(expected_bits, candidate.to_bits_le());
        }
        Ok(())
    }

    #[test]
    fn test_to_bits_be() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a random fixed-length alphanumeric string, that always starts with an alphabetic character.
            let expected_name_string = sample_identifier_as_string::<CurrentNetwork>()?;
            // Recover the field element from the bits.
            let expected_name_field = Field::<CurrentNetwork>::from_bits_le(&expected_name_string.to_bits_le())?;
            let expected_network_field = Field::<CurrentNetwork>::from_bits_le(&"aleo".to_string().to_bits_le())?;
            // Compute the expected bits.
            let mut expected_bits = expected_name_field.to_bits_le()[..expected_name_string.len() * 8]
                .iter()
                .rev()
                .copied()
                .collect::<Vec<_>>();
            expected_bits.extend(expected_network_field.to_bits_le()[..4 * 8].iter().rev().copied());

            let candidate = ProgramID::<CurrentNetwork>::from_str(&format!("{expected_name_string}.aleo"))?;
            assert_eq!(
                expected_name_field.to_bits_le()[..expected_name_string.len() * 8]
                    .iter()
                    .rev()
                    .copied()
                    .collect::<Vec<_>>(),
                candidate.name().to_bits_be()
            );
            assert_eq!(
                expected_network_field.to_bits_le()[..4 * 8].iter().rev().copied().collect::<Vec<_>>(),
                candidate.network().to_bits_be()
            );
            assert_eq!(expected_bits, candidate.to_bits_be());
        }
        Ok(())
    }
}
