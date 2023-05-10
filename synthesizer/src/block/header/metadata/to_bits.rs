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

impl<N: Network> ToBits for Metadata<N> {
    /// Returns the little-endian bits of the metadata.
    fn to_bits_le(&self) -> Vec<bool> {
        vec![
            0u8.to_bits_le(),                               // 1 byte
            self.network.to_bits_le(),                      // 2 bytes
            self.round.to_bits_le(),                        // 8 bytes
            self.height.to_bits_le(),                       // 4 bytes
            self.total_supply_in_microcredits.to_bits_le(), // 8 bytes
            self.cumulative_weight.to_bits_le(),            // 16 bytes
            self.coinbase_target.to_bits_le(),              // 8 bytes
            self.proof_target.to_bits_le(),                 // 8 bytes
            self.last_coinbase_target.to_bits_le(),         // 8 bytes
            self.last_coinbase_timestamp.to_bits_le(),      // 8 bytes
            self.timestamp.to_bits_le(),                    // 8 bytes
        ]
        .concat()
    }

    /// Returns the big-endian bits of the metadata.
    fn to_bits_be(&self) -> Vec<bool> {
        vec![
            0u8.to_bits_be(),                               // 1 byte
            self.network.to_bits_be(),                      // 2 bytes
            self.round.to_bits_be(),                        // 8 bytes
            self.height.to_bits_be(),                       // 4 bytes
            self.total_supply_in_microcredits.to_bits_be(), // 8 bytes
            self.cumulative_weight.to_bits_be(),            // 16 bytes
            self.coinbase_target.to_bits_be(),              // 8 bytes
            self.proof_target.to_bits_be(),                 // 8 bytes
            self.last_coinbase_target.to_bits_be(),         // 8 bytes
            self.last_coinbase_timestamp.to_bits_be(),      // 8 bytes
            self.timestamp.to_bits_be(),                    // 8 bytes
        ]
        .concat()
    }
}
