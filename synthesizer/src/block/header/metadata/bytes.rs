// Copyright (C) 2019-2023 Aleo Systems Inc.
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

impl<N: Network> FromBytes for Metadata<N> {
    /// Reads the metadata from the buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the version.
        let version = u8::read_le(&mut reader)?;
        // Ensure the version is valid.
        if version != 0 {
            return Err(error("Invalid metadata version"));
        }

        // Read from the buffer.
        let network = u16::read_le(&mut reader)?;
        let round = u64::read_le(&mut reader)?;
        let height = u32::read_le(&mut reader)?;
        let total_supply_in_microcredits = u64::read_le(&mut reader)?;
        let cumulative_weight = u128::read_le(&mut reader)?;
        let coinbase_target = u64::read_le(&mut reader)?;
        let proof_target = u64::read_le(&mut reader)?;
        let last_coinbase_target = u64::read_le(&mut reader)?;
        let last_coinbase_timestamp = i64::read_le(&mut reader)?;
        let timestamp = i64::read_le(&mut reader)?;

        // Construct the metadata.
        Self::new(
            network,
            round,
            height,
            total_supply_in_microcredits,
            cumulative_weight,
            coinbase_target,
            proof_target,
            last_coinbase_target,
            last_coinbase_timestamp,
            timestamp,
        )
        .map_err(|e| error(e.to_string()))
    }
}

impl<N: Network> ToBytes for Metadata<N> {
    /// Writes the metadata to the buffer.
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the version.
        0u8.write_le(&mut writer)?;

        // Write to the buffer.
        self.network.write_le(&mut writer)?;
        self.round.write_le(&mut writer)?;
        self.height.write_le(&mut writer)?;
        self.total_supply_in_microcredits.write_le(&mut writer)?;
        self.cumulative_weight.write_le(&mut writer)?;
        self.coinbase_target.write_le(&mut writer)?;
        self.proof_target.write_le(&mut writer)?;
        self.last_coinbase_target.write_le(&mut writer)?;
        self.last_coinbase_timestamp.write_le(&mut writer)?;
        self.timestamp.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_bytes() -> Result<()> {
        let mut rng = TestRng::default();

        for expected in [*crate::vm::test_helpers::sample_genesis_block(&mut rng).metadata()].into_iter() {
            // Check the byte representation.
            let expected_bytes = expected.to_bytes_le()?;
            assert_eq!(expected, Metadata::read_le(&expected_bytes[..])?);
            assert!(Metadata::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());
        }
        Ok(())
    }
}
