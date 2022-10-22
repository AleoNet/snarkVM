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

impl<N: Network> FromBytes for EpochChallenge<N> {
    /// Reads the epoch challenge from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the epoch number.
        let epoch_number = FromBytes::read_le(&mut reader)?;
        // Read the epoch block hash.
        let epoch_block_hash = FromBytes::read_le(&mut reader)?;
        // Read the epoch degree.
        let degree = FromBytes::read_le(&mut reader)?;
        // Return the epoch challenge.
        Self::new(epoch_number, epoch_block_hash, degree).map_err(|e| error(e.to_string()))
    }
}

impl<N: Network> ToBytes for EpochChallenge<N> {
    /// Writes the epoch challenge to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the epoch number.
        self.epoch_number.write_le(&mut writer)?;
        // Write the epoch block hash.
        self.epoch_block_hash.write_le(&mut writer)?;
        // Write the epoch degree.
        self.degree().write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    use rand::RngCore;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: usize = 100;

    #[test]
    fn test_bytes() {
        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a new epoch challenge.
            let degree: u16 = rng.gen(); // Bound the maximal test degree to 2^16.
            let expected = EpochChallenge::<CurrentNetwork>::new(rng.next_u32(), rng.gen(), degree as u32).unwrap();

            // Check the byte representation.
            let expected_bytes = expected.to_bytes_le().unwrap();
            let candidate = EpochChallenge::read_le(&expected_bytes[..]).unwrap();
            assert_eq!(expected.epoch_number(), candidate.epoch_number());
            assert_eq!(expected.epoch_block_hash(), candidate.epoch_block_hash());
            assert_eq!(expected.degree(), candidate.degree());
            assert_eq!(expected, candidate);

            assert!(EpochChallenge::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());
        }
    }
}
