// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::{errors::MerkleTrieError, CRH};
use snarkvm_utilities::{to_bytes_le, ToBytes};

pub trait MerkleTrieParameters: Send + Sync + Clone {
    type H: CRH;

    const MAX_BRANCH: usize;

    const KEY_SIZE: usize;
    const VALUE_SIZE: usize;

    /// Setup the MerkleParameters
    fn setup(message: &str) -> Self;

    /// The maximum depth of the trie derived from `MAX_BRANCH` and `KEY_SIZE`.
    fn max_depth() -> usize {
        let chunk_size = (Self::MAX_BRANCH as f64).log2() as usize;
        (8 * Self::KEY_SIZE + (chunk_size - 1)) / chunk_size
    }

    /// Returns the collision-resistant hash function used by the Merkle tree.
    fn crh(&self) -> &Self::H;

    /// Calculate the root hash of a given node with it's key, value, and children.
    fn hash_node<L: ToBytes>(
        &self,
        key: &Option<Vec<u8>>,
        value: &Option<L>,
        child_roots: &Vec<&<Self::H as CRH>::Output>,
    ) -> Result<<Self::H as CRH>::Output, MerkleTrieError> {
        // Add the current node's key and value to the hash input.
        let mut input = vec![]; // TODO (raychu86): Add the key to the root hash. Full key vs key suffix?
        if let Some(key) = &key {
            let key_bytes = to_bytes_le![key]?;
            input.extend(key_bytes);
        }

        if let Some(value) = &value {
            let value_bytes = to_bytes_le![value]?;
            input.extend(value_bytes);
        }

        // Add the children roots to the hash input.
        for child in child_roots {
            let child_root_bytes = to_bytes_le![child]?;
            input.extend(child_root_bytes);
        }

        for _ in child_roots.len()..Self::MAX_BRANCH {
            let empty_value = <Self::H as CRH>::Output::default().to_bytes_le()?;
            input.extend(&empty_value);
        }

        // Hash the input
        let hash = self.crh().hash(&input)?;

        Ok(hash)
    }
}
