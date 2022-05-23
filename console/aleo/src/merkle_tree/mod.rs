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

mod helpers;
use helpers::*;

mod path;
pub use path::*;

#[cfg(test)]
mod tests;

use crate::Network;
use snarkvm_console_algorithms::{Hash, Poseidon, BHP};
use snarkvm_fields::{One, Zero};
use snarkvm_utilities::{cfg_iter, cfg_iter_mut, ToBits};

use anyhow::{bail, Error, Result};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

#[derive(Default)]
pub struct MerkleTree<N: Network, LH: LeafHash<N>, PH: PathHash<N>, const DEPTH: u8> {
    /// The hash function for the leaf nodes.
    leaf_hasher: LH,
    /// The hash function for the path nodes.
    path_hasher: PH,
    /// The computed root of the full Merkle tree.
    root: N::Field,
    /// The internal hashes, from root to hashed leaves, of the full Merkle tree.
    tree: Vec<N::Field>,
    /// For each level after a full tree has been built from the leaves,
    /// keeps both the roots the siblings that are used to get to the desired depth.
    padding_tree: Vec<(N::Field, N::Field)>,
    /// The (inclusive) starting index of the hashed leaves.
    starting_leaf_index: usize,
    /// The number of hashed leaves in the tree.
    number_of_leaves: usize,
}

impl<N: Network, LH: LeafHash<N>, PH: PathHash<N>, const DEPTH: u8> MerkleTree<N, LH, PH, DEPTH> {
    #[inline]
    pub fn new(leaf_hasher: &LH, path_hasher: &PH, leaves: &[LH::Leaf]) -> Result<Self> {
        // Ensure the DEPTH is non-zero.
        if DEPTH == 0 {
            bail!("The depth of the Merkle tree must be non-zero.");
        }

        // Compute the tree size and tree depth := log2(tree_size).
        let last_level_size = leaves.len().next_power_of_two();
        let tree_size = 2 * last_level_size - 1;
        let tree_depth = tree_depth::<DEPTH>(tree_size)?;

        // Initialize the Merkle tree.
        let empty_hash = path_hasher.hash_empty()?;
        let mut tree = vec![empty_hash; tree_size];

        // Compute the starting index (on the left) for each level of the tree.
        let mut index = 0;
        let mut level_indices = Vec::with_capacity(tree_depth as usize);
        for _ in 0..tree_depth {
            level_indices.push(index);
            index = left_child(index);
        }
        let starting_leaf_index = index;

        // Compute each leaf hash and store it in the bottom row of the Merkle tree.
        if !leaves.is_empty() {
            tree[starting_leaf_index..starting_leaf_index + leaves.len()]
                .copy_from_slice(&Self::hash_leaf_row(&leaf_hasher, leaves)?);
        }

        // Iterate from the bottom row to the top row, computing and storing the hashes of each level.
        let mut end_index = starting_leaf_index;
        for start_index in level_indices.into_iter().rev() {
            // Iterate over the current level.
            if start_index != end_index {
                // Retrieve the children for each node in the current level.
                let pairs =
                    (start_index..end_index).map(|i| (tree[left_child(i)], tree[right_child(i)])).collect::<Vec<_>>();
                // Compute the hashes of the current level.
                tree[start_index..start_index + pairs.len()]
                    .copy_from_slice(&Self::hash_internal_row(&path_hasher, &pairs[..])?);
            }
            // Update the end index for the next level.
            end_index = start_index;
        }

        // Finished computing actual tree.
        // Now, we compute the dummy nodes until we hit our DEPTH goal.
        let mut current_depth = tree_depth;
        let mut padding_tree = Vec::with_capacity(DEPTH.saturating_sub(current_depth + 1) as usize);
        let mut current_hash = tree[0];
        while current_depth < DEPTH {
            current_hash = path_hasher.hash(&current_hash, &empty_hash)?;

            // do not pad at the top-level of the tree
            if current_depth < DEPTH - 1 {
                padding_tree.push((current_hash, empty_hash));
            }
            current_depth += 1;
        }

        Ok(Self {
            leaf_hasher: leaf_hasher.clone(),
            path_hasher: path_hasher.clone(),
            root: current_hash,
            tree,
            padding_tree,
            starting_leaf_index,
            number_of_leaves: leaves.len(),
        })
    }

    #[inline]
    pub fn append(&self, new_leaves: &[LH::Leaf]) -> Result<Self> {
        // Compute the tree size and tree depth := log2(tree_size).
        let last_level_size = (self.number_of_leaves + new_leaves.len()).next_power_of_two();
        let tree_size = 2 * last_level_size - 1;
        let tree_depth = tree_depth::<DEPTH>(tree_size)?;

        // Initialize the Merkle tree.
        let empty_hash = self.path_hasher.hash_empty()?;
        let mut tree = vec![empty_hash; tree_size];

        // Compute the starting index (on the left) for each level of the tree.
        let mut index = 0;
        let mut level_indices = Vec::with_capacity(tree_depth as usize);
        for _ in 0..tree_depth {
            level_indices.push(index);
            index = left_child(index);
        }
        let starting_leaf_index = index;

        // The beginning of the tree can be reconstructed from pre-existing hashed leaves.
        tree[starting_leaf_index..starting_leaf_index + self.number_of_leaves]
            .copy_from_slice(&self.hashed_leaves()[..self.number_of_leaves]);

        // Compute and store the hash values for each leaf.
        if !new_leaves.is_empty() {
            tree[starting_leaf_index + self.number_of_leaves
                ..starting_leaf_index + self.number_of_leaves + new_leaves.len()]
                .copy_from_slice(&Self::hash_leaf_row(&self.leaf_hasher, new_leaves)?);
        }

        // Track the indices of newly added leaves.
        let start_index = self.number_of_leaves;
        let new_indices = || start_index..start_index + new_leaves.len();

        // Compute the hash values for every node in the tree.
        let mut upper_bound = starting_leaf_index;
        for start_index in level_indices.into_iter().rev() {
            let (parents, children) = tree.split_at_mut(upper_bound);

            // Iterate over the current level.
            cfg_iter_mut!(parents[start_index..upper_bound]).zip(start_index..upper_bound).try_for_each(
                |(parent, current_index)| {
                    let left_index = left_child(current_index);
                    let right_index = right_child(current_index);

                    // Hash only the tree paths that are altered by the addition of new leaves or are brand new.
                    if new_indices().contains(&current_index)
                        || self.tree.get(left_index) != children.get(left_index - upper_bound)
                        || self.tree.get(right_index) != children.get(right_index - upper_bound)
                        || new_indices().any(|idx| Ancestors(idx).into_iter().any(|i| i == current_index))
                    {
                        // Compute Hash(left || right).
                        *parent = self
                            .path_hasher
                            .hash(&children[left_index - upper_bound], &children[right_index - upper_bound])?;
                    } else {
                        *parent = self.tree[current_index];
                    }

                    Ok::<(), Error>(())
                },
            )?;
            upper_bound = start_index;
        }

        // Finished computing actual tree.
        // Now, we compute the dummy nodes until we hit our DEPTH goal.
        let mut current_depth = tree_depth;
        let mut current_hash = tree[0];

        // The whole padding tree can be reused if the current hash matches the previous one.
        let padding_tree = if current_hash == self.tree[0] {
            current_hash = self.path_hasher.hash(&self.padding_tree.last().unwrap().0, &empty_hash)?;
            self.padding_tree.clone()
        } else {
            let mut padding_tree = Vec::with_capacity(DEPTH.saturating_sub(current_depth + 1) as usize);
            while current_depth < DEPTH {
                current_hash = self.path_hasher.hash(&current_hash, &empty_hash)?;

                // do not pad at the top-level of the tree
                if current_depth < DEPTH - 1 {
                    padding_tree.push((current_hash, empty_hash));
                }
                current_depth += 1;
            }
            padding_tree
        };

        // update the values at the very end so the original tree is not altered in case of failure
        Ok(Self {
            leaf_hasher: self.leaf_hasher.clone(),
            path_hasher: self.path_hasher.clone(),
            root: current_hash,
            tree,
            padding_tree,
            starting_leaf_index,
            number_of_leaves: self.number_of_leaves + new_leaves.len(),
        })
    }

    /// Returns the Merkle path for the given leaf index and leaf.
    #[inline]
    pub fn prove(&self, leaf_index: usize, leaf: &LH::Leaf) -> Result<MerklePath<N, DEPTH>> {
        // Compute the leaf hash.
        let leaf_hash = self.leaf_hasher.hash(leaf)?;
        // Compute the absolute index of the leaf in the tree.
        let tree_index = self.starting_leaf_index.saturating_add(leaf_index);
        // Ensure the computed tree index contains the given leaf.
        if tree_index >= self.tree.len() || leaf_hash != self.tree[tree_index] {
            bail!("Invalid index detected in the Merkle tree at index {tree_index}");
        }

        // Iterate from the leaf's parent up to the root, storing all intermediate hash values.
        let mut current_node = tree_index;
        let mut path = vec![];

        while !is_root(current_node) {
            let sibling_node = sibling(current_node).unwrap();
            path.push(self.tree[sibling_node]);
            current_node = parent(current_node).unwrap();

            // Ensure the Merkle path is within the depth bound.
            if path.len() > DEPTH as usize {
                bail!("Merkle path cannot exceed depth {DEPTH}: attempted to reach depth {}", path.len())
            }
        }

        if path.len() != DEPTH as usize {
            path.push(self.path_hasher.hash_empty()?);

            for &(ref _hash, ref sibling_hash) in &self.padding_tree {
                path.push(*sibling_hash);
            }
        }

        MerklePath::try_from((path, leaf_index as u64))
    }

    #[inline]
    pub const fn root(&self) -> &N::Field {
        &self.root
    }

    #[inline]
    pub fn tree(&self) -> &[N::Field] {
        &self.tree
    }

    #[inline]
    pub fn hashed_leaves(&self) -> &[N::Field] {
        &self.tree[self.starting_leaf_index..]
    }

    #[inline]
    fn hash_leaf_row(leaf_hasher: &LH, leaf_nodes: &[LH::Leaf]) -> Result<Vec<N::Field>> {
        match leaf_nodes.len() {
            0 => Ok(vec![]),
            1 => Ok(vec![leaf_hasher.hash(&leaf_nodes[0])?]),
            _ => cfg_iter!(leaf_nodes).map(|leaf| leaf_hasher.hash(&leaf)).collect(),
        }
    }

    #[inline]
    fn hash_internal_row(path_hasher: &PH, internal_nodes: &[(N::Field, N::Field)]) -> Result<Vec<N::Field>> {
        match internal_nodes.len() {
            0 => Ok(vec![]),
            1 => Ok(vec![path_hasher.hash(&internal_nodes[0].0, &internal_nodes[0].1)?]),
            _ => cfg_iter!(internal_nodes).map(|(left, right)| path_hasher.hash(left, right)).collect(),
        }
    }
}

/// Returns the depth of the tree, given the size of the tree.
#[inline]
fn tree_depth<const DEPTH: u8>(tree_size: usize) -> Result<u8> {
    // Ensure the tree size is less than 2^52 (for casting to an f64).
    let tree_depth = match tree_size < 4503599627370496 {
        // Compute the log2 of the tree size.
        true => (tree_size as f64).log2(),
        false => bail!("Tree size must be less than 2^52"),
    };
    // Ensure the tree depth is within a u8 range.
    match tree_depth <= u8::MAX as f64 {
        // Ensure the tree depth is within the depth bound.
        true => match tree_depth as u8 <= DEPTH {
            // Return the tree depth.
            true => Ok(tree_depth as u8),
            false => bail!("Merkle tree cannot exceed depth {DEPTH}: attempted to reach depth {tree_depth}"),
        },
        false => bail!("Merkle tree depth exceeds maximum size: {}", tree_depth),
    }
}

/// Returns true iff the index represents the root.
#[inline]
const fn is_root(index: usize) -> bool {
    index == 0
}

/// Returns the index of the left child, given an index.
#[inline]
const fn left_child(index: usize) -> usize {
    2 * index + 1
}

/// Returns the index of the right child, given an index.
#[inline]
const fn right_child(index: usize) -> usize {
    2 * index + 2
}

/// Returns the index of the sibling, given an index.
#[inline]
const fn sibling(index: usize) -> Option<usize> {
    if is_root(index) {
        None
    } else if is_left_child(index) {
        Some(index + 1)
    } else {
        Some(index - 1)
    }
}

/// Returns true iff the given index represents a left child.
#[inline]
const fn is_left_child(index: usize) -> bool {
    index % 2 == 1
}

/// Returns the index of the parent, given an index.
#[inline]
const fn parent(index: usize) -> Option<usize> {
    if index > 0 { Some((index - 1) >> 1) } else { None }
}

pub struct Ancestors(usize);

impl Iterator for Ancestors {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        if let Some(parent) = parent(self.0) {
            self.0 = parent;
            Some(parent)
        } else {
            None
        }
    }
}
