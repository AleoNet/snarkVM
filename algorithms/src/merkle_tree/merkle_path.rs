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

use crate::{
    errors::MerkleError,
    traits::{MerkleParameters, CRH},
};
use snarkvm_utilities::{error, FromBytes, FromBytesDeserializer, ToBytes, ToBytesSerializer};

use anyhow::Result;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::{
    io::{Read, Result as IoResult, Write},
    sync::Arc,
};

pub type MerkleTreeDigest<P> = <<P as MerkleParameters>::TwoToOneCRH as CRH>::Output;

/// Stores the hashes of a particular path (in order) from leaf to root.
/// Our path `is_left_child()` if the boolean in `path` is true.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerklePath<P: MerkleParameters> {
    pub parameters: Arc<P>,
    pub path: Vec<MerkleTreeDigest<P>>,
    pub leaf_index: u64,
}

impl<P: MerkleParameters> MerklePath<P> {
    /// Returns a new instance of a Merkle path.
    pub fn from(parameters: Arc<P>, path: Vec<MerkleTreeDigest<P>>, leaf_index: u64) -> Result<Self> {
        Ok(Self { parameters, path, leaf_index })
    }

    pub fn verify<L: ToBytes>(&self, root_hash: &MerkleTreeDigest<P>, leaf: &L) -> Result<bool, MerkleError> {
        // Check that the given leaf matches the leaf in the membership proof.
        if self.path.len() == P::DEPTH {
            let claimed_leaf_hash = self.parameters.hash_leaf::<L>(leaf)?;

            let mut index = self.leaf_index;
            let mut curr_path_node = claimed_leaf_hash;

            // Check levels between leaf level and root.
            for level in 0..self.path.len() {
                // Check if path node at this level is left or right.
                let (left_bytes, right_bytes) =
                    Self::select_left_right_bytes(index, &curr_path_node, &self.path[level])?;
                // Update the current path node.
                curr_path_node = self.parameters.hash_inner_node(&left_bytes, &right_bytes)?;
                index >>= 1;
            }

            // Check if final hash is root
            if &curr_path_node != root_hash {
                return Ok(false);
            }

            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Convert `computed_hash` and `sibling_hash` to bytes. `index` is the first `path.len()` bits of
    /// the position of tree.
    ///
    /// If the least significant bit of `index` is 0, then `input_1` will be left and `input_2` will be right.
    /// Otherwise, `input_1` will be right and `input_2` will be left.
    ///
    /// Returns: (left, right)
    fn select_left_right_bytes(
        index: u64,
        computed_hash: &<P::TwoToOneCRH as CRH>::Output,
        sibling_hash: &<P::TwoToOneCRH as CRH>::Output,
    ) -> Result<(<P::TwoToOneCRH as CRH>::Output, <P::TwoToOneCRH as CRH>::Output), MerkleError> {
        let is_left = index & 1 == 0;
        let mut left_bytes = computed_hash;
        let mut right_bytes = sibling_hash;
        if !is_left {
            core::mem::swap(&mut left_bytes, &mut right_bytes);
        }
        Ok((*left_bytes, *right_bytes))
    }

    /// The position of on_path node in `leaf_and_sibling_hash` and `non_leaf_and_sibling_hash_path`.
    /// `position[i]` is 0 (false) iff `i`th on-path node from top to bottom is on the left.
    ///
    /// This function simply converts `self.leaf_index` to boolean array in big endian form.
    pub fn position_list(&self) -> impl Iterator<Item = bool> + '_ {
        (0..self.path.len()).map(move |i| ((self.leaf_index >> i) & 1) != 0)
    }
}

// TODO (howardwu): TEMPORARY - Deprecate this with a ledger rearchitecture.
impl<P: MerkleParameters> Default for MerklePath<P> {
    fn default() -> Self {
        let mut path = Vec::with_capacity(P::DEPTH);
        for _i in 0..P::DEPTH {
            path.push(MerkleTreeDigest::<P>::default());
        }
        Self { parameters: Arc::new(P::setup("unsafe")), path, leaf_index: 0 }
    }
}

impl<P: MerkleParameters> FromBytes for MerklePath<P> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // TODO (howardwu): TEMPORARY - This is a temporary fix to support ToBytes/FromBytes for
        //  LedgerProof and LocalProof. While it is "safe", it is not performant to deserialize
        //  in such a manual fashion. However, given the extent to which modifying the architecture
        //  of Merkle trees in snarkVM impacts many APIs downstream, this forward-compatible change
        //  is being introduced until a proper refactor can be discussed and implemented.
        //  If you are seeing this message, please be proactive in bringing it up :)
        let parameters = {
            // Decode the setup message size.
            let setup_message_length = u16::read_le(&mut reader)?;

            let mut setup_message_bytes = vec![0u8; setup_message_length as usize];
            reader.read_exact(&mut setup_message_bytes)?;
            let setup_message = String::from_utf8(setup_message_bytes)
                .map_err(|_| error("Failed to parse setup message for Merkle parameters"))?;

            Arc::new(P::setup(&setup_message))
        };

        // Decode the Merkle path depth.
        let path_length: u8 = FromBytes::read_le(&mut reader)?;

        let mut path = Vec::with_capacity(path_length as usize);
        for _ in 0..path_length {
            path.push(FromBytes::read_le(&mut reader)?);
        }

        let leaf_index: u64 = FromBytes::read_le(&mut reader)?;

        Ok(Self { parameters, path, leaf_index })
    }
}

impl<P: MerkleParameters> ToBytes for MerklePath<P> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        let setup_message_bytes: &[u8] = self.parameters.setup_message().as_bytes();

        // Ensure the setup message size is within bounds.
        if setup_message_bytes.len() > (u16::MAX as usize) {
            return Err(error(format!("Merkle path setup message cannot exceed {} bytes", u16::MAX)));
        }

        // Encode the setup message.
        (setup_message_bytes.len() as u16).write_le(&mut writer)?;
        setup_message_bytes.write_le(&mut writer)?;

        // Ensure the Merkle path length is within bounds.
        if self.path.len() > (u8::MAX as usize) {
            return Err(error(format!("Merkle path depth cannot exceed {}", u8::MAX)));
        }

        // Encode the Merkle path.
        (self.path.len() as u8).write_le(&mut writer)?;
        self.path.write_le(&mut writer)?;

        self.leaf_index.write_le(&mut writer)
    }
}

impl<P: MerkleParameters> Serialize for MerklePath<P> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        ToBytesSerializer::serialize_with_size_encoding(self, serializer)
    }
}

impl<'de, P: MerkleParameters> Deserialize<'de> for MerklePath<P> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "Merkle path")
    }
}
