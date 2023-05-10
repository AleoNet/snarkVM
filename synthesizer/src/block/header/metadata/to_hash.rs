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

impl<N: Network> Metadata<N> {
    /// Returns the metadata hash.
    pub fn to_hash(&self) -> Result<Field<N>> {
        // Construct the metadata bits (the last leaf in the Merkle tree).
        let metadata_bits = self.to_bits_le(); // 632 bits
        // Ensure the metadata bits is the correct size.
        ensure!(metadata_bits.len() == 632, "Incorrect metadata size");
        // Hash the metadata bits.
        let metadata_hash = N::hash_bhp512(&metadata_bits)?;
        // Return the metadata hash.
        Ok(metadata_hash)
    }
}
