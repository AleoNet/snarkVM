// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

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
        self.0.to_bits_le()[..8 * self.1 as usize].to_vec()
    }

    /// Returns the big-endian bits of the identifier.
    fn to_bits_be(&self) -> Vec<bool> {
        let mut bits = self.to_bits_le();
        bits.reverse();
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
        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a random fixed-length alphanumeric string, that always starts with an alphabetic character.
            let expected_string = sample_identifier_as_string::<CurrentNetwork>(&mut rng)?;
            // Recover the field element from the bits.
            let expected_field = Field::<CurrentNetwork>::from_bits_le(&expected_string.to_bits_le())?;

            let candidate = Identifier::<CurrentNetwork>::from_str(&expected_string)?;
            assert_eq!(expected_field, candidate.0);
            assert_eq!(expected_field.to_bits_le()[..expected_string.len() * 8], candidate.to_bits_le());
        }
        Ok(())
    }

    #[test]
    fn test_to_bits_be() -> Result<()> {
        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a random fixed-length alphanumeric string, that always starts with an alphabetic character.
            let expected_string = sample_identifier_as_string::<CurrentNetwork>(&mut rng)?;
            // Recover the field element from the bits.
            let expected_field = Field::<CurrentNetwork>::from_bits_le(&expected_string.to_bits_le())?;

            let candidate = Identifier::<CurrentNetwork>::from_str(&expected_string)?;
            assert_eq!(expected_field, candidate.0);
            assert_eq!(
                expected_field.to_bits_le()[..expected_string.len() * 8].iter().rev().copied().collect::<Vec<_>>(),
                candidate.to_bits_be()
            );
        }
        Ok(())
    }
}
