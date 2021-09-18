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

use crate::{errors::MerkleError, traits::CRH};
use snarkvm_utilities::{to_bytes_le, ToBytes};

use std::{collections::BTreeMap, fmt::Debug, sync::Arc};

#[derive(Default)]
pub struct MerkleTrie<P: CRH, T: Debug> {
    /// The CRH used to create the root hash.
    parameters: Arc<P>,
    /// The root hash of the Merkle trie.
    root: [u8; 32],
    /// The key of the current Merkle trie.
    key: Vec<u8>,
    /// The value existing at the current Merkle trie node.
    value: Option<T>,
    /// Any child Merkle tries. Currently has u8::MAX potential branches.
    children: BTreeMap<u8, MerkleTrie<P, T>>, // TODO (raychu86): Remove the current duplication of parameters.
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

impl<P: CRH, T: ToBytes + Debug> MerkleTrie<P, T> {
    /// Create a new Merkle trie.
    pub fn new(parameters: Arc<P>) -> Result<Self, MerkleError> {
        let merkle_trie = Self {
            parameters,
            root: [0u8; 32],
            key: Vec::new(),
            value: None,
            children: BTreeMap::new(),
        };

        Ok(merkle_trie)
    }

    /// Check if the Merkle trie is empty.
    pub fn is_empty(&self) -> bool {
        self.root == [0u8; 32] && self.value.is_none() && self.children.is_empty()
    }

    /// Insert a (key, value) pair into the Merkle trie.
    pub fn insert(&mut self, key: &[u8], value: Option<T>) -> Result<(), MerkleError> {
        // If the trie is currently empty, set the key value pair.
        if self.is_empty() {
            self.key = key.to_vec();
            self.value = value;
            self.update_root()?;
            return Ok(());
        }

        // Get the length of the prefix match to derive the prefix and suffix/
        let prefix_length = get_matching_prefix_length(&self.key, key);
        let prefix = key[0..prefix_length].to_vec();
        let suffix = key[prefix_length..].to_vec();

        // If the prefix exists outside the key of the current key.
        if prefix_length >= self.key.len() {
            // If the match length is equal to the length of the root key, then attempt to insert.
            if prefix_length == key.len() {
                if self.value.is_some() {
                    // TODO (raychu86): Update the Error type.
                    return Err(MerkleError::Message("Key already exists".to_string()));
                }

                self.value = value;
            } else {
                // Insert a child trie based on the suffix.
                self.insert_child(&suffix, value.unwrap())?;
            }
        } else {
            // If the prefix exists within the key of the current trie.
            // Build the new subtrie.
            let mut new_node = MerkleTrie::<P, T> {
                parameters: self.parameters.clone(),
                key: suffix.clone(),
                root: [0u8; 32],
                value: self.value.take(),
                children: BTreeMap::new(),
            };

            // Swap the current node's and the new node's children.
            std::mem::swap(&mut new_node.children, &mut self.children);
            // Update the `root` of the new node.
            new_node.update_root()?;

            // Update the original trie key, and children.
            self.key = prefix;
            self.value = None;
            self.children = BTreeMap::new(); // This line is not necessary because of the mem swap.
            self.children.insert(new_node.key[0], new_node);

            // Update the values if we have found the correct node.
            if prefix_length == key.len() {
                // Update the value in the current node if the key matches.
                self.value = value;
            } else {
                // Update the value in a subtrie node.
                self.insert_child(&suffix, value.unwrap())?;
            }
        }

        self.update_root()?;

        Ok(())
    }

    /// Helper function to insert a (key, value) pair into the current Merkle trie node.
    fn insert_child(&mut self, suffix: &Vec<u8>, value: T) -> Result<(), MerkleError> {
        // Check the first element of the suffix.
        match self.children.get_mut(&suffix[0]) {
            None => {
                // No child tree for this suffix exists yet.
                // Crate a new subtree.
                let mut new_child = MerkleTrie::new(self.parameters.clone())?;
                new_child.insert(&suffix, Some(value))?;

                // Insert the new subtree into the current tree.
                self.children.insert(new_child.key[0], new_child);
            }
            Some(child_trie) => {
                // The child tree already exists.
                // Insert the (suffix, value) pair to the child tree.
                child_trie.insert(&suffix, Some(value))?;
            }
        }

        Ok(())
    }

    /// Update the root of the Merkle trie with it's current children.
    fn update_root(&mut self) -> Result<(), MerkleError> {
        if self.is_empty() {
            self.root = [0; 32];
        } else {
            // TODO (raychu86): Determine if hasing the key is required.

            // Add the current node's key and value to the hash input.
            let mut input = self.key.to_vec();
            if let Some(value) = &self.value {
                let value_bytes = to_bytes_le![value]?;
                input.extend(value_bytes);
            }

            // Add the children roots to the hash input.
            for child in self.children.values() {
                input.extend(child.root());
            }

            // Hash the input
            let hash = self.parameters.hash(&input)?;
            let hash_bytes = to_bytes_le![hash]?;
            let mut root = [0u8; 32];
            root.copy_from_slice(&hash_bytes);

            // Update the new root.
            self.root = root;
        }

        Ok(())
    }

    // fn get(&self, key: &[u8]) -> Option<&T> {
    //     unimplemented!()
    // }
    //
    // fn remove(&mut self, key: &[u8]) -> Option<T> {
    //     unimplemented!()
    // }
    //

    #[inline]
    pub fn root(&self) -> &[u8; 32] {
        &self.root
    }

    //
    // pub fn generate_proof<L: ToBytes>(&self, index: usize, leaf: &L) -> Result<MerklePath<P>, MerkleError> {
    //     unimplemented!()
    // }
}
