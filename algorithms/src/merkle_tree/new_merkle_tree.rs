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
    merkle_tree::{MerklePath, MerkleTreeDigest},
    traits::{MerkleParameters, CRH},
};
use snarkvm_utilities::ToBytes;
use std::sync::Arc;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

#[derive(Default)]
pub struct NewMerkleTree<P: MerkleParameters> {
    /// The computed root of the full Merkle tree.
    root: MerkleTreeDigest<P>,
    /// The internal hashes of the full Merkle tree.
    non_leaf_nodes: Vec<MerkleTreeDigest<P>>,
    /// The hashed leaf nodes.
    leaf_nodes: Vec<MerkleTreeDigest<P>>,
    /// For each level after a full tree has been built from the leaves,
    /// keeps both the roots the siblings that are used to get to the desired depth.
    padding_tree: Vec<(MerkleTreeDigest<P>, MerkleTreeDigest<P>)>,
    /// The Merkle tree parameters (e.g. the hash function).
    parameters: Arc<P>,
}

impl<P: MerkleParameters + Send + Sync> NewMerkleTree<P> {
    pub const DEPTH: usize = P::DEPTH;

    pub fn new<L: ToBytes + Send + Sync>(parameters: Arc<P>, leaves: &[L]) -> Result<Self, MerkleError> {
        let new_time = start_timer!(|| "MerkleTree::new");

        let last_level_size = leaves.len().next_power_of_two();
        let tree_size = 2 * last_level_size - 1;
        let tree_depth = tree_depth(tree_size);

        if tree_depth > Self::DEPTH {
            return Err(MerkleError::InvalidTreeDepth(tree_depth, Self::DEPTH));
        }

        let mut leaf_digests = Self::hash_row(&*parameters, &leaves)?;
        leaf_digests.resize(last_level_size, Default::default());

        let leaf_nodes_size = leaf_digests.len();
        let non_leaf_nodes_size = leaf_nodes_size - 1;

        let empty_hash = parameters.hash_empty()?;

        // Initialize the merkle tree as array of nodes in level order
        let mut non_leaf_nodes = (0..non_leaf_nodes_size).map(|_| empty_hash).collect::<Vec<_>>();

        // Compute the starting indices for each non-leaf level of the tree
        let mut index = 0;
        let mut level_indices = Vec::with_capacity(tree_depth);
        for _ in 0..(tree_depth) {
            level_indices.push(index);
            index = left_child(index);
        }

        // Compute the hash values for the non-leaf bottom layer
        if let Some(start_index) = level_indices.pop() {
            let upper_bound = left_child(start_index);
            for current_index in start_index..upper_bound {
                // `left_child(current_index)` and `right_child(current_index) returns the position of
                // leaf in the whole tree (represented as a list in level order). We need to shift it
                // by `-upper_bound` to get the index in `leaf_nodes` list.
                let left_leaf_index = left_child(current_index) - upper_bound;
                let right_leaf_index = right_child(current_index) - upper_bound;
                // compute hash

                non_leaf_nodes[current_index] =
                    parameters.hash_inner_node(&leaf_digests[left_leaf_index], &leaf_digests[right_leaf_index])?
            }
        }

        // Compute the hash values for nodes in every other layer in the tree
        level_indices.reverse();
        for &start_index in &level_indices {
            // The layer beginning `start_index` ends at `upper_bound` (exclusive).
            let upper_bound = left_child(start_index);
            for current_index in start_index..upper_bound {
                let left_index = left_child(current_index);
                let right_index = right_child(current_index);
                non_leaf_nodes[current_index] =
                    parameters.hash_inner_node(&non_leaf_nodes[left_index], &non_leaf_nodes[right_index])?
            }
        }

        // Finished computing actual tree.
        // Now, we compute the dummy nodes until we hit our DEPTH goal.
        let mut current_depth = tree_depth;
        let mut padding_tree = Vec::with_capacity((Self::DEPTH).saturating_sub(current_depth + 1));
        let mut current_hash = if !non_leaf_nodes.is_empty() { non_leaf_nodes[0] } else { empty_hash };
        while current_depth < Self::DEPTH {
            current_hash = parameters.hash_inner_node(&current_hash, &empty_hash)?;

            // do not pad at the top-level of the tree
            if current_depth < Self::DEPTH - 1 {
                padding_tree.push((current_hash, empty_hash));
            }
            current_depth += 1;
        }
        let root = current_hash;

        end_timer!(new_time);

        Ok(Self { leaf_nodes: leaf_digests, non_leaf_nodes, padding_tree, parameters, root })
    }

    pub fn rebuild<L: ToBytes + Send + Sync>(&self, start_index: usize, new_leaves: &[L]) -> Result<Self, MerkleError> {
        let new_time = start_timer!(|| "MerkleTree::rebuild");

        let last_level_size = (start_index + new_leaves.len()).next_power_of_two();
        let tree_size = 2 * last_level_size - 1;
        let tree_depth = tree_depth(tree_size);

        if tree_depth > Self::DEPTH {
            return Err(MerkleError::InvalidTreeDepth(tree_depth, Self::DEPTH));
        }

        // Initialize the Merkle tree.
        let empty_hash = self.parameters.hash_empty()?;
        let mut tree = self.non_leaf_nodes.clone();

        // Compute the starting index (on the left) for each level of the tree.
        let mut index = 0;
        let mut level_indices = Vec::with_capacity(tree_depth);
        for _ in 0..tree_depth {
            level_indices.push(index);
            index = left_child(index);
        }

        // Compute and store the hash values for each leaf.
        // let last_level_index = level_indices.pop().unwrap_or(0);

        // The beginning of the tree can be reconstructed from pre-existing hashed leaves.
        // tree[last_level_index..][..start_index].clone_from_slice(&self.hashed_leaves()[..start_index]);

        // The new leaves require hashing.
        let subsection = Self::hash_row(&*self.parameters, new_leaves)?;

        let mut leaf_nodes = self.leaf_nodes.clone();

        // Optimize this. Don't need to store the full power of 2.
        leaf_nodes.resize(last_level_size, empty_hash);
        leaf_nodes[start_index..][..subsection.len()].clone_from_slice(&subsection[..]);

        let non_leaf_nodes_size = leaf_nodes.len() - 1;
        let old_tree_size = self.non_leaf_nodes.len();
        tree.resize(non_leaf_nodes_size, empty_hash);

        // Track the indices of newly added non leaf nodes.
        let new_indices = || old_tree_size..non_leaf_nodes_size;

        // TODO (raychu86) Optimize this.
        // Compute the hash values for the non-leaf bottom layer
        if let Some(start_index) = level_indices.pop() {
            let upper_bound = left_child(start_index);
            crate::cfg_iter_mut!(tree[start_index..upper_bound]).zip(start_index..upper_bound).try_for_each(
                |(node, current_index)| {
                    // `left_child(current_index)` and `right_child(current_index) returns the position of
                    // leaf in the whole tree (represented as a list in level order). We need to shift it
                    // by `-upper_bound` to get the index in `leaf_nodes` list.
                    let left_leaf_index = left_child(current_index) - upper_bound;
                    let right_leaf_index = right_child(current_index) - upper_bound;

                    if self.leaf_nodes.get(left_leaf_index) != leaf_nodes.get(left_leaf_index)
                        || self.non_leaf_nodes.get(right_leaf_index) != leaf_nodes.get(right_leaf_index)
                    {
                        *node = self
                            .parameters
                            .hash_inner_node(&leaf_nodes[left_leaf_index], &leaf_nodes[right_leaf_index])?;
                    } else {
                        *node = self.non_leaf_nodes[current_index];
                    }

                    Ok::<(), MerkleError>(())
                },
            )?;
        }

        for start_index in level_indices.into_iter().rev() {
            // The layer beginning `start_index` ends at `upper_bound` (exclusive).
            let upper_bound = left_child(start_index);

            let (parents, children) = tree.split_at_mut(upper_bound);

            // Iterate over the current level.
            crate::cfg_iter_mut!(parents[start_index..upper_bound]).zip(start_index..upper_bound).try_for_each(
                |(parent, current_index)| {
                    let left_index = left_child(current_index);
                    let right_index = right_child(current_index);

                    // Hash only the tree paths that are altered by the addition of new leaves or are brand new.
                    if new_indices().contains(&current_index)
                        || self.non_leaf_nodes.get(left_index) != children.get(left_index - upper_bound)
                        || self.non_leaf_nodes.get(right_index) != children.get(right_index - upper_bound)
                        || new_indices().any(|idx| Ancestors(idx).into_iter().any(|i| i == current_index))
                    {
                        // Compute Hash(left || right).
                        *parent = self.parameters.hash_inner_node(
                            &children[left_index - upper_bound],
                            &children[right_index - upper_bound],
                        )?;
                    } else {
                        *parent = self.non_leaf_nodes[current_index];
                    }

                    Ok::<(), MerkleError>(())
                },
            )?;
        }

        // Finished computing actual tree.
        // Now, we compute the dummy nodes until we hit our DEPTH goal.
        let mut current_depth = tree_depth;
        let mut current_hash = if !tree.is_empty() { tree[0] } else { empty_hash.clone() };

        let non_leaf_root = if !self.non_leaf_nodes.is_empty() { self.non_leaf_nodes[0] } else { empty_hash.clone() };

        // The whole padding tree can be reused if the current hash matches the previous one.
        let new_padding_tree = if current_hash == non_leaf_root {
            current_hash = self.parameters.hash_inner_node(&self.padding_tree.last().unwrap().0, &empty_hash)?;

            None
        } else {
            let mut padding_tree = Vec::with_capacity((Self::DEPTH).saturating_sub(current_depth + 1));

            while current_depth < Self::DEPTH {
                current_hash = self.parameters.hash_inner_node(&current_hash, &empty_hash)?;

                // do not pad at the top-level of the tree
                if current_depth < Self::DEPTH - 1 {
                    padding_tree.push((current_hash, empty_hash));
                }
                current_depth += 1;
            }

            Some(padding_tree)
        };
        let root = current_hash;

        end_timer!(new_time);

        // update the values at the very end so the original tree is not altered in case of failure
        Ok(Self {
            root,
            non_leaf_nodes: tree,
            leaf_nodes,
            padding_tree: if let Some(padding_tree) = new_padding_tree {
                padding_tree
            } else {
                self.padding_tree.clone()
            },
            parameters: self.parameters.clone(),
        })
    }

    #[inline]
    pub fn root(&self) -> &<P::H as CRH>::Output {
        &self.root
    }

    #[inline]
    pub fn non_leaf_nodes(&self) -> &[<P::H as CRH>::Output] {
        &self.non_leaf_nodes
    }

    #[inline]
    pub fn hashed_leaves(&self) -> &[<P::H as CRH>::Output] {
        &self.leaf_nodes
    }

    pub fn generate_proof<L: ToBytes>(&self, index: usize, leaf: &L) -> Result<MerklePath<P>, MerkleError> {
        let prove_time = start_timer!(|| "MerkleTree::generate_proof");

        let leaf_hash = self.parameters.hash_leaf(leaf)?;

        let last_level_size = self.leaf_nodes.len();
        let tree_size = 2 * last_level_size - 1;
        let tree_depth = tree_depth(tree_size);
        let tree_index = convert_index_to_last_level(index, tree_depth)?;

        // if tree_index >= self.non_leaf_nodes.len() || leaf_hash != self.leaf_nodes[index] {
        //     return Err(MerkleError::IncorrectLeafIndex(tree_index));
        // }

        if leaf_hash != self.leaf_nodes[index] {
            return Err(MerkleError::IncorrectLeafIndex(tree_index));
        }

        let leaf_sibling_hash = if index & 1 == 0 {
            // leaf is left child
            self.leaf_nodes[index + 1]
        } else {
            // leaf is right child
            self.leaf_nodes[index - 1]
        };

        // path.len() = `tree height - 2`, the two missing elements being the leaf sibling hash and the root
        let mut path = vec![leaf_sibling_hash];
        // Iterate from the bottom layer after the leaves, to the top, storing all sibling node's hash values.
        let mut current_node = parent(tree_index).unwrap();

        while !is_root(current_node) {
            let sibling_node = sibling(current_node).unwrap();
            path.push(self.non_leaf_nodes[sibling_node]);
            current_node = parent(current_node).unwrap();
        }

        assert_eq!(path.len(), tree_depth);

        // Store the root node. Set boolean as true for consistency with digest location.
        if path.len() > Self::DEPTH {
            return Err(MerkleError::InvalidPathLength(path.len(), Self::DEPTH));
        }

        if path.len() != Self::DEPTH {
            let empty_hash = self.parameters.hash_empty()?;
            path.push(empty_hash);

            for &(ref _hash, ref sibling_hash) in &self.padding_tree {
                path.push(*sibling_hash);
            }
        }

        end_timer!(prove_time);

        if path.len() != Self::DEPTH {
            Err(MerkleError::IncorrectPathLength(path.len()))
        } else {
            Ok(MerklePath { parameters: self.parameters.clone(), path, leaf_index: index as u64 })
        }
    }

    fn hash_row<L: ToBytes + Send + Sync>(
        parameters: &P,
        leaves: &[L],
    ) -> Result<Vec<<<P as MerkleParameters>::H as CRH>::Output>, MerkleError> {
        match leaves.len() {
            0 => Ok(vec![]),
            _ => Ok(crate::cfg_iter!(leaves).map(|leaf| parameters.hash_leaf(&leaf).unwrap()).collect::<Vec<_>>()),
        }
    }
}

/// Returns the depth of the tree, given the size of the tree.
#[inline]
fn tree_depth(tree_size: usize) -> usize {
    // Returns the log2 value of the given number.
    fn log2(number: usize) -> usize {
        (number as f64).log2() as usize
    }

    log2(tree_size)
}

/// Returns true iff the index represents the root.
#[inline]
fn is_root(index: usize) -> bool {
    index == 0
}

/// Returns the index of the left child, given an index.
#[inline]
fn left_child(index: usize) -> usize {
    2 * index + 1
}

/// Returns the index of the right child, given an index.
#[inline]
fn right_child(index: usize) -> usize {
    2 * index + 2
}

/// Returns the index of the sibling, given an index.
#[inline]
fn sibling(index: usize) -> Option<usize> {
    if index == 0 {
        None
    } else if is_left_child(index) {
        Some(index + 1)
    } else {
        Some(index - 1)
    }
}

/// Returns true iff the given index represents a left child.
#[inline]
fn is_left_child(index: usize) -> bool {
    index % 2 == 1
}

/// Returns the index of the parent, given an index.
#[inline]
fn parent(index: usize) -> Option<usize> {
    if index > 0 { Some((index - 1) >> 1) } else { None }
}

#[inline]
fn convert_index_to_last_level(index: usize, tree_depth: usize) -> Result<usize, MerkleError> {
    let shifted = 1u32.checked_shl(tree_depth as u32).ok_or(MerkleError::IncorrectLeafIndex(index))?;
    Ok(index.saturating_add(shifted as usize).saturating_sub(1))
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
