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

impl<N: Network> Metadata<N> {
    /// Returns the metadata hash.
    pub fn to_hash(&self) -> Result<Field<N>> {
        // Construct the metadata bits (the last leaf in the Merkle tree).
        let metadata_bits = self.to_bits_le(); // 760 bits
        // Ensure the metadata bits is the correct size.
        ensure!(metadata_bits.len() == 760, "Incorrect metadata size");
        // Hash the metadata bits.
        let metadata_hash = N::hash_bhp512(&metadata_bits)?;
        // Return the metadata hash.
        Ok(metadata_hash)
    }
}
