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

use crate::{
    errors::MerkleTrieError,
    merkle_trie::{MerkleTrieDigest, MerkleTrieNode, MerkleTriePath},
    traits::MerkleTrieParameters,
};
use snarkvm_utilities::{from_bits_le_to_bytes_le, from_bytes_le_to_bits_le, ToBytes};

use std::{collections::BTreeMap, sync::Arc};

#[derive(Default, Clone)]
pub struct MerkleTrie<P: MerkleTrieParameters, T: ToBytes + PartialEq + Clone> {
    /// The CRH used to create the root hash.
    pub(crate) parameters: Arc<P>,
    pub(crate) node: MerkleTrieNode<P, T>,
}

impl<P: MerkleTrieParameters, T: ToBytes + PartialEq + Clone> MerkleTrie<P, T> {
    pub const MAX_BRANCH: usize = P::MAX_BRANCH;

    /// Create a new Merkle trie.
    pub fn new(parameters: Arc<P>, key_pairs: Vec<(Vec<u8>, T)>) -> Result<Self, MerkleTrieError> {
        let mut merkle_trie = Self {
            parameters,
            node: MerkleTrieNode {
                root: MerkleTrieDigest::<P>::default(),
                key: Vec::new(),
                full_key: None,
                value: None,
                children: BTreeMap::new(),
            },
        };

        for (key, value) in key_pairs {
            merkle_trie.insert(&key, value)?;
        }

        Ok(merkle_trie)
    }

    /// Check if the Merkle trie is empty.
    pub fn is_empty(&self) -> bool {
        self.node.is_empty()
    }

    /// Insert a (key, value) pair into the Merkle trie.
    pub fn insert(&mut self, key: &[u8], value: T) -> Result<(), MerkleTrieError> {
        assert_eq!(key.len(), P::KEY_SIZE);

        // Translate the key to match the branching factor.
        let translated_key = translate_key::<P>(key)?;

        self.node.insert(&self.parameters, &translated_key, key, value)
    }

    /// Get a value given a key.
    pub fn get(&self, key: &[u8]) -> Option<&T> {
        assert_eq!(key.len(), P::KEY_SIZE);

        // Translate the key to match the branching factor.
        let translated_key = translate_key::<P>(key).unwrap();

        self.node.get(&translated_key)
    }

    /// Remove the value at a given key. Returns the value if it was removed successfully, and None
    /// if there was no value associated to the given key.
    pub fn remove(&mut self, key: &[u8]) -> Result<Option<T>, MerkleTrieError> {
        assert_eq!(key.len(), P::KEY_SIZE);

        // Translate the key to match the branching factor.
        let translated_key = translate_key::<P>(key)?;

        self.node.remove(&self.parameters, &translated_key)
    }

    pub fn generate_proof(&self, key: &[u8], value: &T) -> Result<MerkleTriePath<P>, MerkleTrieError> {
        let prove_time = start_timer!(|| "MerkleTrie::generate_proof");

        // Check that the key pair exists.
        if let Some(expected_value) = self.get(key) {
            if value != expected_value {
                return Err(MerkleTrieError::IncorrectKey(key.to_vec()));
            }
        } else {
            let expected_key = &translate_key::<P>(key).unwrap()[..];

            return Err(MerkleTrieError::MissingLeaf(expected_key.to_vec()));
        }

        let mut path = vec![];
        let mut traversal = vec![];

        let mut temp_key = self.node.key.clone();
        let mut temp_children = &self.node.children;

        let mut expected_key = &translate_key::<P>(key).unwrap()[..];

        // Traverse the children until the key/value pair is found.
        let mut found = false;
        while !found {
            if expected_key.len() == 1 && temp_key == expected_key {
                found = true;
            } else {
                // If the given key starts with the root key.

                let index = temp_children.keys().position(|&r| r == expected_key[0]).unwrap();
                let mut siblings: Vec<MerkleTrieDigest<P>> =
                    temp_children.iter().map(|(_x, trie)| trie.root().clone()).collect();
                siblings.remove(index);

                traversal.push(index as u8);
                path.push(siblings);

                if let Some(child_node) = temp_children.get(&expected_key[0]) {
                    temp_children = &child_node.children;
                    temp_key = child_node.key.clone();
                }

                expected_key = &expected_key[1..];
            }
        }

        // Reverse the vectors to start from the leaf.
        path.reverse();
        traversal.reverse();

        end_timer!(prove_time);

        let proof = MerkleTriePath {
            parameters: self.parameters.clone(),
            path,
            traversal,
        };

        Ok(proof)
    }

    /// Returns the root hash of the Merkle trie.
    #[inline]
    pub fn root(&self) -> &MerkleTrieDigest<P> {
        self.node.root()
    }
}

/// Translate the given key to a format that aligns with the branching factor.
pub fn translate_key<P: MerkleTrieParameters>(key: &[u8]) -> Result<Vec<u8>, MerkleTrieError> {
    // Get the number of bits required for the branch size.
    let chunk_size_bits = (P::MAX_BRANCH as f64).log2() as usize;

    // Convert the key to bits.
    let key_bits = from_bytes_le_to_bits_le(key).collect::<Vec<bool>>();

    // Map the bits to the new chunk_size.
    let new_bit_chunks = key_bits
        .chunks(chunk_size_bits)
        .map(|bits| bits.to_vec())
        .collect::<Vec<Vec<bool>>>();

    // Construct the new bytes from the boolean inputs.
    let new_bytes = new_bit_chunks
        .iter()
        .map(|bits| from_bits_le_to_bytes_le(bits))
        .collect::<Vec<Vec<u8>>>();

    // Translate the key.
    let translated_key = new_bytes.into_iter().flatten().collect::<Vec<u8>>();

    assert_eq!(translated_key.len(), P::max_depth());

    Ok(translated_key)
}
