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
    /// The key of the current Merkle trie.
    pub(crate) key: Vec<u8>, // TODO (raychu86): Enforce a max depth size (bound by the length of the key).
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

            let root = parameters.hash_node(&self.key, &self.value, &child_roots)?;

            // Update the new root.
            self.root = root;
        }

        Ok(())
    }

    /// Insert a (key, value) pair into the Merkle trie.
    pub fn insert(&mut self, parameters: &P, key: &[u8], value: T) -> Result<(), MerkleTrieError> {
        assert_eq!(value.to_bytes_le()?.len(), P::VALUE_SIZE);

        // If the trie is currently empty, set the key value pair.
        if self.is_empty() {
            self.key = key.to_vec();
            self.value = Some(value);
            self.update_root(parameters)?;
            return Ok(());
        }

        // Get the length of the prefix match to derive the prefix and suffix/
        let prefix_length = get_matching_prefix_length(&self.key, key);
        let prefix = key[0..prefix_length].to_vec();
        let suffix = key[prefix_length..].to_vec();

        // If the prefix exists outside the key of the current key.
        if prefix_length >= self.key.len() {
            // If the match length is equal to the length of the root key, then attempt to insert.
            if prefix_length == key.len() && prefix == self.key {
                if self.value.is_some() {
                    // TODO (raychu86): Update the Error type.
                    return Err(MerkleTrieError::Message("Key already exists".to_string()));
                }

                self.value = Some(value);
            } else {
                // Insert a child trie based on the suffix.
                self.insert_child(parameters, &suffix, value)?;
            }
        } else {
            let old_key_prefix = self.key[0..prefix_length].to_vec();
            let old_key_suffix = self.key[prefix_length..].to_vec();

            // If the prefix exists within the key of the current trie.
            // Build the new subtrie.
            let mut new_node = MerkleTrieNode::<P, T> {
                key: old_key_suffix.clone(),
                root: MerkleTrieDigest::<P>::default(),
                value: self.value.take(),
                children: BTreeMap::new(),
            };

            // Swap the current node's and the new node's children.
            std::mem::swap(&mut new_node.children, &mut self.children);
            // Update the `root` of the new node.
            new_node.update_root(parameters)?;

            // Update the original trie key, and children.
            self.key = old_key_prefix;
            self.value = None;
            self.children = BTreeMap::new(); // This line is not necessary because of the mem swap.
            self.children.insert(new_node.key[0], new_node);

            // Update the values if we have found the correct node.
            if prefix_length == key.len() {
                // Update the value in the current node if the key matches.
                self.value = Some(value);
            } else {
                // Update the value in a subtrie node.
                self.insert_child(parameters, &suffix, value)?;
            }
        }

        self.update_root(parameters)?;

        Ok(())
    }

    /// Get a value given a key.
    pub fn get(&self, key: &[u8]) -> Option<&T> {
        // If the key is the root, return the value.
        if self.key == key {
            return self.value.as_ref();
        } else if key.starts_with(&self.key) {
            // If the given key starts with the root key.
            let suffix = &key[self.key.len()..];

            return match self.children.get(&suffix[0]) {
                Some(child_node) => child_node.get(&suffix),
                None => None,
            };
        }

        None
    }

    /// Remove the value at a given key. Returns the value if it was removed successfully, and None
    /// if there was no value associated to the given key.
    pub fn remove(&mut self, parameters: &P, key: &[u8]) -> Result<Option<T>, MerkleTrieError> {
        // If the node key is empty or is a subset of the given key.
        if key.starts_with(&self.key) || self.key.is_empty() {
            // If the key is the same.
            if key == self.key {
                let value = self.value.take();
                self.value = None;
                self.compress(parameters)?;
                return Ok(value);
            } else if self.key.len() <= key.len() {
                // If the current node is a parent, find it's child.
                let suffix = &key[self.key.len()..];

                // If a child with the suffix exists, then remove it.
                if let Some(child_node) = self.children.get_mut(&suffix[0]) {
                    // Attempt to remove the node with the suffix
                    match child_node.remove(parameters, &suffix)? {
                        Some(value) => {
                            // If there was a value removed, then remove the child from the list of children.
                            self.children.remove(&suffix[0]);

                            self.compress(parameters)?;
                            return Ok(Some(value));
                        }
                        None => return Ok(None),
                    }
                }
            }
        }

        Ok(None)
    }

    /// Insert a (key, value) pair into the current Merkle trie node.
    fn insert_child(&mut self, parameters: &P, suffix: &Vec<u8>, value: T) -> Result<(), MerkleTrieError> {
        // Check the first element of the suffix.
        match self.children.get_mut(&suffix[0]) {
            None => {
                // No child tree for this suffix exists yet.
                // Crate a new subtree.
                let mut new_child = Self {
                    root: MerkleTrieDigest::<P>::default(),
                    key: Vec::new(),
                    value: None,
                    children: BTreeMap::new(),
                };
                new_child.insert(parameters, &suffix, value)?;

                // Insert the new subtree into the current tree.
                self.children.insert(new_child.key[0], new_child);
            }
            Some(child_trie) => {
                // The child tree already exists.
                // Insert the (suffix, value) pair to the child tree.
                child_trie.insert(parameters, &suffix, value)?;
            }
        }

        Ok(())
    }

    /// Compress the node under 2 conditions.
    /// 1. It is empty.
    /// 2. It has no value, and only 1 child.
    fn compress(&mut self, parameters: &P) -> Result<(), MerkleTrieError> {
        // If the node is empty, clear the key.
        if self.is_empty() {
            self.key.clear();
            self.update_root(parameters)?;
        } else if self.value.is_none() && self.children.len() == 1 {
            // If the value is none and there is only 1 child, then move the child up.
            let child = self.children.values().next().unwrap();

            // Append the child key to the current key.
            self.key.extend_from_slice(&child.key);
            self.value = child.value.clone();
            self.children = child.children.clone();

            self.update_root(parameters)?;
        }

        Ok(())
    }

    /// Check if the Merkle trie is empty.
    pub fn is_empty(&self) -> bool {
        self.root == MerkleTrieDigest::<P>::default() && self.value.is_none() && self.children.is_empty()
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
