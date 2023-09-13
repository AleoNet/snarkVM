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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct KAryMerklePath<E: Environment, H: Clone + PartialEq + Send + Sync, const DEPTH: u8, const ARITY: u8> {
    /// The leaf index for the path.
    leaf_index: U64<E>,
    /// The `siblings` contains a list of sibling hashes from the leaf to the root.
    siblings: Vec<Vec<H>>,
}

impl<E: Environment, H: Clone + PartialEq + Send + Sync, const DEPTH: u8, const ARITY: u8>
    TryFrom<(U64<E>, Vec<Vec<H>>)> for KAryMerklePath<E, H, DEPTH, ARITY>
{
    type Error = Error;

    /// Returns a new instance of a Merkle path.
    fn try_from((leaf_index, siblings): (U64<E>, Vec<Vec<H>>)) -> Result<Self> {
        // Ensure the Merkle tree depth is greater than 0.
        ensure!(DEPTH > 0, "Merkle tree depth must be greater than 0");
        // Ensure the Merkle tree depth is less than or equal to 64.
        ensure!(DEPTH <= 64u8, "Merkle tree depth must be less than or equal to 64");
        // Ensure the Merkle tree arity is greater than 1.
        ensure!(ARITY > 1, "Merkle tree arity must be greater than 1");
        // Ensure the leaf index is within the tree depth.
        ensure!((*leaf_index as u128) < (ARITY as u128).pow(DEPTH as u32), "Found an out of bounds Merkle leaf index");
        // Ensure the Merkle path is the correct length.
        ensure!(siblings.len() == DEPTH as usize, "Found an incorrect Merkle path length");
        for sibling in &siblings {
            ensure!(sibling.len() == ARITY.saturating_sub(1) as usize, "Found an incorrect Merkle path arity");
        }
        // Return the Merkle path.
        Ok(Self { leaf_index, siblings })
    }
}

impl<E: Environment, H: Clone + PartialEq + Send + Sync, const DEPTH: u8, const ARITY: u8>
    KAryMerklePath<E, H, DEPTH, ARITY>
{
    /// Returns the leaf index for the path.
    pub fn leaf_index(&self) -> U64<E> {
        self.leaf_index
    }

    /// Returns the siblings for the path.
    pub fn siblings(&self) -> &[Vec<H>] {
        &self.siblings
    }

    /// Returns `true` if the Merkle path is valid for the given root and leaf.
    pub fn verify<LH: LeafHash<Hash = PH::Hash>, PH: PathHash<Hash = H>>(
        &self,
        leaf_hasher: &LH,
        path_hasher: &PH,
        root: &PH::Hash,
        leaf: &LH::Leaf,
    ) -> bool {
        // Ensure the leaf index is within the tree depth.
        if (*self.leaf_index as u128) >= (ARITY as u128).checked_pow(DEPTH as u32).unwrap_or(u128::MAX) {
            eprintln!("Found an out of bounds Merkle leaf index");
            return false;
        }
        // Ensure the path length matches the expected depth.
        if self.siblings.len() != DEPTH as usize {
            eprintln!("Found an incorrect Merkle path length");
            return false;
        }

        // Initialize a tracker for the current hash, by computing the leaf hash to start.
        let mut current_hash = match leaf_hasher.hash_leaf(leaf) {
            Ok(candidate_leaf_hash) => candidate_leaf_hash,
            Err(error) => {
                eprintln!("Failed to hash the Merkle leaf during verification: {error}");
                return false;
            }
        };

        // Compute the ordering of the current hash and sibling hashes on each level.
        // The indicator index determines which sibling the current hash is.
        let indicator_indexes: Vec<usize> = match (0..DEPTH)
            .map(|i| usize::try_from(*self.leaf_index as u128 / (ARITY as u128).pow(i as u32) % ARITY as u128))
            .collect::<Result<Vec<_>, _>>()
        {
            Ok(indexes) => indexes,
            _ => {
                eprintln!("Found an incorrect Merkle leaf index");
                return false;
            }
        };

        // Check levels between leaf level and root.
        for (indicator_index, sibling_hashes) in indicator_indexes.into_iter().zip_eq(&self.siblings) {
            // Construct the ordering of sibling hashes for this level.
            let mut sibling_hashes = sibling_hashes.clone();

            // Insert the current hash into the list of sibling hashes.
            sibling_hashes.insert(indicator_index, current_hash);

            // Update the current hash for the next level.
            match path_hasher.hash_children(&sibling_hashes) {
                Ok(hash) => current_hash = hash,
                Err(error) => {
                    eprintln!("Failed to hash the Merkle path during verification: {error}");
                    return false;
                }
            }
        }

        // Ensure the final hash matches the given root.
        current_hash == *root
    }
}
//
// impl<E: Environment, const DEPTH: u8, const ARITY: u8> FromBytes for KAryMerklePath<E, DEPTH, ARITY> {
//     /// Reads in a Merkle path from a buffer.
//     #[inline]
//     fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
//         // Read the leaf index.
//         let leaf_index = u64::read_le(&mut reader)?;
//         // Read the Merkle path siblings.
//         let siblings = (0..DEPTH)
//             .map(|_| (0..ARITY).map(|_| Ok(Field::new(FromBytes::read_le(&mut reader)?))).collect::<IoResult<Vec<_>>>())
//             .collect::<IoResult<Vec<_>>>()?;
//         // Return the Merkle path.
//         Self::try_from((U64::new(leaf_index), siblings)).map_err(|err| error(err.to_string()))
//     }
// }
//
// impl<E: Environment, const DEPTH: u8, const ARITY: u8> ToBytes for KAryMerklePath<E, DEPTH, ARITY> {
//     /// Writes the Merkle path to a buffer.
//     #[inline]
//     fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
//         // Write the leaf index.
//         self.leaf_index.write_le(&mut writer)?;
//         // Write the Merkle path siblings.
//         self.siblings
//             .iter()
//             .try_for_each(|siblings| siblings.iter().try_for_each(|sibling| sibling.write_le(&mut writer)))
//     }
// }
//
// impl<E: Environment, const DEPTH: u8, const ARITY: u8> Serialize for KAryMerklePath<E, DEPTH, ARITY> {
//     fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
//         ToBytesSerializer::serialize(self, serializer)
//     }
// }
//
// impl<'de, E: Environment, const DEPTH: u8, const ARITY: u8> Deserialize<'de> for KAryMerklePath<E, DEPTH, ARITY> {
//     fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
//         // Compute the size for: u64 + (Field::SIZE_IN_BYTES * DEPTH * (ARITY - 1)).
//         let size = 8 + DEPTH as usize * (ARITY.saturating_sub(1) as usize) * (Field::<E>::size_in_bits() + 7) / 8;
//         FromBytesDeserializer::<Self>::deserialize(deserializer, "Merkle path", size)
//     }
// }
