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
use snarkvm_utilities::{
    error,
    io::{Read, Result as IoResult, Write},
    FromBytes,
    FromBytesDeserializer,
    ToBytes,
    ToBytesSerializer,
};

use anyhow::Result;
use core::marker::PhantomData;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// Stores the hashes of a particular path (in order) from leaf to root.
/// Our path `is_left_child()` if the boolean in `path` is true.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerklePath<N: Network, LH: LeafHash<N>, PH: PathHash<N>, const DEPTH: u8> {
    path: Vec<N::Field>,
    leaf_index: u64,
    _phantom: PhantomData<(LH, PH)>,
}

impl<N: Network, LH: LeafHash<N>, PH: PathHash<N>, const DEPTH: u8> TryFrom<(Vec<N::Field>, u64)>
    for MerklePath<N, LH, PH, DEPTH>
{
    type Error = Error;

    /// Returns a new instance of a Merkle path.
    fn try_from((path, leaf_index): (Vec<N::Field>, u64)) -> Result<Self> {
        // Ensure the Merkle path is the correct length.
        match path.len() == DEPTH as usize {
            // Return the Merkle path.
            true => Ok(Self { path, leaf_index, _phantom: PhantomData }),
            false => bail!("Expected a Merkle path of length {DEPTH}, found length {}", path.len()),
        }
    }
}

impl<N: Network, LH: LeafHash<N>, PH: PathHash<N>, const DEPTH: u8> MerklePath<N, LH, PH, DEPTH> {
    /// Returns `true` if the Merkle path is valid for the given root and leaf.
    pub fn verify(&self, leaf_hasher: &LH, path_hasher: &PH, root_hash: &N::Field, leaf: &LH::Leaf) -> bool {
        // Ensure the path length matches the expected depth.
        if self.path.len() != DEPTH as usize {
            return false;
        }

        // Compute the leaf hash, and return `false` on failure.
        let claimed_leaf_hash = match leaf_hasher.hash(leaf) {
            Ok(hash) => hash,
            Err(error) => {
                eprintln!("Failed to hash leaf during Merkle path verification: {error}");
                return false;
            }
        };

        let mut index = self.leaf_index;
        let mut current_hash = claimed_leaf_hash;

        // Check levels between leaf level and root.
        for level in 0..self.path.len() {
            // Check if path node at this level is left or right.
            let (left, right) = Self::select_left_right(index, &current_hash, &self.path[level]);
            // Update the current path node.
            match path_hasher.hash(&left, &right) {
                Ok(hash) => current_hash = hash,
                Err(error) => {
                    eprintln!("Failed to hash path node during Merkle path verification: {error}");
                    return false;
                }
            }
            index >>= 1;
        }

        // Check if final hash is root.
        current_hash == *root_hash
    }

    /// Convert `computed_hash` and `sibling_hash` to bytes. `index` is the first `path.len()` bits of
    /// the position of tree.
    ///
    /// If the least significant bit of `index` is 0, then `input_1` will be left and `input_2` will be right.
    /// Otherwise, `input_1` will be right and `input_2` will be left.
    ///
    /// Returns: (left, right)
    fn select_left_right(index: u64, computed_hash: &N::Field, sibling_hash: &N::Field) -> (N::Field, N::Field) {
        let is_left = index & 1 == 0;
        let mut left = computed_hash;
        let mut right = sibling_hash;
        if !is_left {
            core::mem::swap(&mut left, &mut right);
        }
        (*left, *right)
    }

    /// The position of on_path node in `leaf_and_sibling_hash` and `non_leaf_and_sibling_hash_path`.
    /// `position[i]` is 0 (false) iff `i`th on-path node from top to bottom is on the left.
    ///
    /// This function simply converts `self.leaf_index` to boolean array in big endian form.
    pub fn position_list(&self) -> impl Iterator<Item = bool> + '_ {
        (0..self.path.len()).map(move |i| ((self.leaf_index >> i) & 1) != 0)
    }
}

impl<N: Network, LH: LeafHash<N>, PH: PathHash<N>, const DEPTH: u8> FromBytes for MerklePath<N, LH, PH, DEPTH> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the Merkle path.
        let path_length: u8 = FromBytes::read_le(&mut reader)?;
        let path = (0..path_length).map(|_| N::Field::read_le(&mut reader)).collect::<IoResult<Vec<_>>>()?;
        // Read the leaf index.
        let leaf_index: u64 = FromBytes::read_le(&mut reader)?;

        Self::try_from((path, leaf_index)).map_err(|err| error(err.to_string()))
    }
}

impl<N: Network, LH: LeafHash<N>, PH: PathHash<N>, const DEPTH: u8> ToBytes for MerklePath<N, LH, PH, DEPTH> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the Merkle path length is within bounds.
        if self.path.len() > (u8::MAX as usize) {
            return Err(error(format!("Merkle path depth cannot exceed {}", u8::MAX)));
        }

        // Write the Merkle path.
        (self.path.len() as u8).write_le(&mut writer)?;
        self.path.write_le(&mut writer)?;
        // Write the leaf index.
        self.leaf_index.write_le(&mut writer)
    }
}

impl<N: Network, LH: LeafHash<N>, PH: PathHash<N>, const DEPTH: u8> Serialize for MerklePath<N, LH, PH, DEPTH> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        ToBytesSerializer::serialize_with_size_encoding(self, serializer)
    }
}

impl<'de, N: Network, LH: LeafHash<N>, PH: PathHash<N>, const DEPTH: u8> Deserialize<'de>
    for MerklePath<N, LH, PH, DEPTH>
{
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "Merkle path")
    }
}
