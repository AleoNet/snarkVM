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

use crate::{errors::MerkleTrieError, merkle_trie::MerkleTrieDigest, traits::MerkleTrieParameters};
use snarkvm_utilities::ToBytes;

use std::collections::BTreeMap;

#[derive(Default, Clone)]
pub struct MerkleTrieNode<P: MerkleTrieParameters, T: ToBytes + PartialEq + Clone> {
    /// The root hash of the Merkle trie.
    pub(crate) root: MerkleTrieDigest<P>,
    /// The key of the current Merkle node.
    pub(crate) key: Vec<u8>,
    /// The full non-truncated key of the key/value pair inserted into the merkle trie.
    pub(crate) full_key: Option<Vec<u8>>, // TODO (raychu86): Enforce a max depth size (bound by the length of the key).
    /// The value existing at the current Merkle trie node.
    pub(crate) value: Option<T>,
    /// Any child Merkle tries. Currently has u8::MAX potential branches. // TODO (raychu86): Allow for generic branch sizes.
    pub(crate) children: BTreeMap<u8, MerkleTrieNode<P, T>>,
}

impl<P: MerkleTrieParameters, T: ToBytes + PartialEq + Clone> MerkleTrieNode<P, T> {
    /// Update the root of the Merkle trie using its current children.
    fn update_root(&mut self, parameters: &P) -> Result<(), MerkleTrieError> {
        if self.is_empty() {
            self.root = MerkleTrieDigest::<P>::default();
        } else {
            // Add the children roots to the hash input.
            let mut child_roots = vec![];
            for child in self.children.values() {
                child_roots.push(child.root());
            }

            let root = match self.full_key.is_some() && self.value.is_some() {
                true => parameters.hash_leaf(&self.full_key, &self.value)?,
                false => parameters.hash_node(&child_roots)?,
            };

            // Update the new root.
            self.root = root;
        }

        Ok(())
    }

    /// Insert a (key, value) pair into the Merkle trie.
    pub fn insert(&mut self, parameters: &P, key: &[u8], full_key: &[u8], value: T) -> Result<(), MerkleTrieError> {
        assert_eq!(value.to_bytes_le()?.len(), P::VALUE_SIZE);

        // If the trie is at the leaf
        if key.len() == 1 {
            if self.value.is_some() || self.full_key.is_some() {
                // TODO (raychu86): Update the Error type.
                return Err(MerkleTrieError::Message("Key already exists".to_string()));
            }
            self.key = vec![key[0]];
            self.full_key = Some(full_key.to_vec());
            self.value = Some(value);
        } else {
            // If a child path exists, then insert it into this child.
            if let Some(child) = self.children.get_mut(&key[0]) {
                child.insert(parameters, &key[1..], full_key, value)?;
            } else {
                // If the prefix exists within the key of the current trie.
                // Build the new subtrie.
                let mut new_node = MerkleTrieNode::<P, T> {
                    root: MerkleTrieDigest::<P>::default(),
                    key: vec![key[0]],
                    full_key: None,
                    value: None,
                    children: BTreeMap::new(),
                };

                new_node.insert(parameters, &key[1..], full_key, value)?;
                self.children.insert(key[0], new_node);
            }
        }
        self.update_root(parameters)?;

        Ok(())
    }

    /// Get a value given a key.
    pub fn get(&self, key: &[u8]) -> Option<&T> {
        // If the key is the root, return the value.
        if key.len() == 1 && self.key == key {
            self.value.as_ref()
        } else {
            return match self.children.get(&key[0]) {
                Some(child_node) => child_node.get(&key[1..]),
                None => None,
            };
        }
    }

    /// Remove the value at a given key. Returns the value if it was removed successfully, and None
    /// if there was no value associated to the given key.
    pub fn remove(&mut self, parameters: &P, key: &[u8]) -> Result<Option<T>, MerkleTrieError> {
        // // If the node key is empty or is a subset of the given key.
        // if key.starts_with(&self.key) || self.key.is_empty() {
        //     // If the key is the same.
        //     if key == self.key {
        //         let value = self.value.take();
        //         self.full_key = None;
        //         self.value = None;
        //         self.compress(parameters)?;
        //         return Ok(value);
        //     } else if self.key.len() < key.len() {
        //         // If the current node is a parent, find it's child.
        //         let suffix = &key[self.key.len()..];
        //
        //         // If a child with the suffix exists, then remove it.
        //         if let Some(child_node) = self.children.get_mut(&suffix[0]) {
        //             // Attempt to remove the node with the suffix
        //             match child_node.remove(parameters, &suffix)? {
        //                 Some(value) => {
        //                     // If there was a value removed, then remove the child from the list of children (if it is empty).
        //                     if child_node.is_empty() {
        //                         self.children.remove(&suffix[0]);
        //                     }
        //
        //                     self.compress(parameters)?;
        //                     return Ok(Some(value));
        //                 }
        //                 None => return Ok(None),
        //             }
        //         }
        //     }
        // }

        Ok(None)
    }

    /// Compress the node under 2 conditions.
    /// 1. It is empty.
    /// 2. It has no value, and only 1 child.
    fn compress(&mut self, parameters: &P) -> Result<(), MerkleTrieError> {
        // // If the node is empty, clear the key.
        // if self.is_empty() {
        //     self.key.clear();
        //     self.update_root(parameters)?;
        // } else if self.value.is_none() && self.children.len() == 1 {
        //     // If the value is none and there is only 1 child, then move the child up.
        //     let child = self.children.values().next().unwrap();
        //
        //     // Append the child key to the current key.
        //     self.key.extend_from_slice(&child.key);
        //     self.full_key = child.full_key.clone();
        //     self.value = child.value.clone();
        //     self.children = child.children.clone();
        //
        //     self.update_root(parameters)?;
        // }

        Ok(())
    }

    /// Check if the Merkle trie is empty.
    pub fn is_empty(&self) -> bool {
        self.root == MerkleTrieDigest::<P>::default()
            && self.full_key.is_none()
            && self.value.is_none()
            && self.children.is_empty()
    }

    /// Returns the root hash of the Merkle trie node.
    #[inline]
    pub fn root(&self) -> &MerkleTrieDigest<P> {
        &self.root
    }
}

/// Number of prefix elements the two keys have in common.
pub fn get_matching_prefix_length(key: &[u8], key_2: &[u8]) -> usize {
    let mut count: usize = 0;
    // Iterate over both keys. End on the first difference or if one of the keys is empty.
    for (elem_1, elem_2) in key.iter().zip(key_2) {
        if elem_1 == elem_2 {
            count += 1;
        } else {
            break;
        }
    }

    count
}
