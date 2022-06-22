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
pub use helpers::*;

mod path;
pub use path::*;

#[cfg(test)]
mod tests;

use snarkvm_console_types::prelude::*;

use aleo_std::prelude::*;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

#[derive(Clone)]
pub struct MerkleTree<E: Environment, LH: LeafHash<Hash = PH::Hash>, PH: PathHash<Hash = Field<E>>, const DEPTH: u8> {
    /// The leaf hasher for the Merkle tree.
    leaf_hasher: LH,
    /// The path hasher for the Merkle tree.
    path_hasher: PH,
    /// The computed root of the full Merkle tree.
    root: PH::Hash,
    /// The internal hashes, from root to hashed leaves, of the full Merkle tree.
    tree: Vec<PH::Hash>,
    /// The canonical empty hash.
    empty_hash: Field<E>,
    /// The number of hashed leaves in the tree.
    number_of_leaves: usize,
}

impl<E: Environment, LH: LeafHash<Hash = PH::Hash>, PH: PathHash<Hash = Field<E>>, const DEPTH: u8>
    MerkleTree<E, LH, PH, DEPTH>
{
    #[timed]
    #[inline]
    /// Initializes a new Merkle tree with the given leaves.
    pub fn new(leaf_hasher: &LH, path_hasher: &PH, leaves: &[LH::Leaf]) -> Result<Self> {
        // Ensure the Merkle tree depth is greater than 0.
        ensure!(DEPTH > 0, "Merkle tree depth must be greater than 0");
        // Ensure the Merkle tree depth is less than or equal to 64.
        ensure!(DEPTH <= 64u8, "Merkle tree depth must be less than or equal to 64");

        // Compute the maximum number of leaves.
        let max_leaves = leaves.len().next_power_of_two();
        // Compute the number of nodes.
        let num_nodes = max_leaves - 1;
        // Compute the tree size as the maximum number of leaves plus the number of nodes.
        let tree_size = max_leaves + num_nodes;
        // Compute the number of levels in the Merkle tree (i.e. log2(tree_size)).
        let tree_depth = tree_depth::<DEPTH>(tree_size)?;
        // Compute the number of padded levels.
        let padding_depth = DEPTH - tree_depth;

        // Compute the empty hash.
        let empty_hash = path_hasher.hash_empty()?;

        // Initialize the Merkle tree.
        let mut tree = vec![empty_hash; tree_size];

        // Compute and store each leaf hash.
        tree[num_nodes..num_nodes + leaves.len()].copy_from_slice(&leaf_hasher.hash_leaves(leaves)?);

        // Compute and store the hashes for each level, iterating from the penultimate level to the root level.
        let mut start_index = num_nodes;
        // Compute the start index of the current level.
        while let Some(start) = parent(start_index) {
            // Compute the end index of the current level.
            let end = left_child(start);
            // Construct the children for each node in the current level.
            let tuples = (start..end).map(|i| (tree[left_child(i)], tree[right_child(i)])).collect::<Vec<_>>();
            // Compute and store the hashes for each node in the current level.
            tree[start..end].copy_from_slice(&path_hasher.hash_all_children(&tuples)?);
            // Update the start index for the next level.
            start_index = start;
        }

        // Compute the root hash, by iterating from the root level up to `DEPTH`.
        let mut root_hash = tree[0];
        for _ in 0..padding_depth {
            // Update the root hash, by hashing the current root hash with the empty hash.
            root_hash = path_hasher.hash_children(&root_hash, &empty_hash)?;
        }

        Ok(Self {
            leaf_hasher: leaf_hasher.clone(),
            path_hasher: path_hasher.clone(),
            root: root_hash,
            tree,
            empty_hash,
            number_of_leaves: leaves.len(),
        })
    }

    #[timed]
    #[inline]
    /// Returns a new Merkle tree with the given new leaves appended to it.
    pub fn append(&mut self, new_leaves: &[LH::Leaf]) -> Result<()> {
        // Compute the maximum number of leaves.
        let max_leaves = (self.number_of_leaves + new_leaves.len()).next_power_of_two();
        // Compute the number of nodes.
        let num_nodes = max_leaves - 1;
        // Compute the tree size as the maximum number of leaves plus the number of nodes.
        let tree_size = max_leaves + num_nodes;
        // Compute the number of levels in the Merkle tree (i.e. log2(tree_size)).
        let tree_depth = tree_depth::<DEPTH>(tree_size)?;
        // Compute the number of padded levels.
        let padding_depth = DEPTH - tree_depth;

        // Initialize the Merkle tree.
        let mut tree = vec![self.empty_hash; num_nodes];
        // Extend the new Merkle tree with the existing leaf hashes.
        tree.extend(self.leaf_hashes());
        // Extend the new Merkle tree with the new leaf hashes.
        tree.extend(&self.leaf_hasher.hash_leaves(new_leaves)?);
        // Resize the new Merkle tree with empty hashes to pad up to `tree_size`.
        tree.resize(tree_size, self.empty_hash);

        // Initialize a timer for the while loop.
        let timer = timer!("while");

        // Initialize a precompute index to track the starting index of each precomputed level.
        let mut precompute_index = self.number_of_leaves.next_power_of_two() - 1;
        // Initialize a start index to track the starting index of the current level.
        let mut start_index = num_nodes;
        // Initialize a middle index to separate the precomputed indices from the new indices that need to be computed.
        let mut middle_index = num_nodes + self.number_of_leaves;

        // Compute and store the hashes for each level, iterating from the penultimate level to the root level.
        while let (Some(start), Some(middle)) = (parent(start_index), parent(middle_index)) {
            // Compute the end index of the current level.
            let end = left_child(start);

            // If the current level has precomputed indices, copy them instead of recomputing them.
            if let Some(precompute_start) = parent(precompute_index) {
                // Compute the end index of the precomputed level.
                let precompute_end = precompute_start + (middle - start);
                // Copy the hashes for each node in the current level.
                tree[start..middle].copy_from_slice(&self.tree[precompute_start..precompute_end]);
                // Update the precompute index for the next level.
                precompute_index = precompute_start;
            } else {
                // Ensure the start index is equal to the middle index, as all precomputed indices have been processed.
                ensure!(start == middle, "Failed to process all precomputed indices in the Merkle tree");
            }
            lap!(timer, "Precompute: {start} -> {middle}");

            // Construct the children for the new indices in the current level.
            let tuples = (middle..end).map(|i| (tree[left_child(i)], tree[right_child(i)])).collect::<Vec<_>>();
            // Process the indices that need to be computed for the current level.
            // If any level requires computing more than 100 nodes, borrow the tree for performance.
            match tuples.len() >= 100 {
                // Option 1: Borrow the tree to compute and store the hashes for the new indices in the current level.
                true => cfg_iter_mut!(tree[middle..end]).zip_eq(cfg_iter!(tuples)).try_for_each(
                    |(node, (left, right))| {
                        *node = self.path_hasher.hash_children(left, right)?;
                        Ok::<_, Error>(())
                    },
                )?,
                // Option 2: Compute and store the hashes for the new indices in the current level.
                false => tree[middle..end].iter_mut().zip_eq(&tuples).try_for_each(|(node, (left, right))| {
                    *node = self.path_hasher.hash_children(left, right)?;
                    Ok::<_, Error>(())
                })?,
            }
            lap!(timer, "Compute: {middle} -> {end}");

            // Update the start index for the next level.
            start_index = start;
            // Update the middle index for the next level.
            middle_index = middle;
        }

        // End the timer for the while loop.
        finish!(timer);

        // Compute the root hash, by iterating from the root level up to `DEPTH`.
        let mut root_hash = tree[0];
        for _ in 0..padding_depth {
            // Update the root hash, by hashing the current root hash with the empty hash.
            root_hash = self.path_hasher.hash_children(&root_hash, &self.empty_hash)?;
        }

        // update the values at the very end so the original tree is not altered in case of failure
        *self = Self {
            leaf_hasher: self.leaf_hasher.clone(),
            path_hasher: self.path_hasher.clone(),
            root: root_hash,
            tree,
            empty_hash: self.empty_hash,
            number_of_leaves: self.number_of_leaves + new_leaves.len(),
        };
        Ok(())
    }

    #[inline]
    /// Returns the Merkle path for the given leaf index and leaf.
    pub fn prove(&self, leaf_index: usize, leaf: &LH::Leaf) -> Result<MerklePath<E, DEPTH>> {
        // Ensure the leaf index is valid.
        ensure!(leaf_index < self.number_of_leaves, "The given Merkle leaf index is out of bounds");

        // Compute the leaf hash.
        let leaf_hash = self.leaf_hasher.hash_leaf(leaf)?;

        // Compute the start index (on the left) for the leaf hashes level in the Merkle tree.
        let start = self.number_of_leaves.next_power_of_two() - 1;
        // Compute the absolute index of the leaf in the Merkle tree.
        let mut index = start + leaf_index;
        // Ensure the leaf index is valid.
        ensure!(index < self.tree.len(), "The given Merkle leaf index is out of bounds");
        // Ensure the leaf hash matches the one in the tree.
        ensure!(self.tree[index] == leaf_hash, "The given Merkle leaf does not match the one in the Merkle tree");

        // Initialize a vector for the Merkle path.
        let mut path = Vec::with_capacity(DEPTH as usize);

        // Iterate from the leaf hash to the root level, storing the sibling hashes along the path.
        for _ in 0..DEPTH {
            // Compute the index of the sibling hash, if it exists.
            if let Some(sibling) = sibling(index) {
                // Append the sibling hash to the path.
                path.push(self.tree[sibling]);
                // Compute the index of the parent hash, if it exists.
                match parent(index) {
                    // Update the index to the parent index.
                    Some(parent) => index = parent,
                    // If the parent does not exist, the path is complete.
                    None => break,
                }
            }
        }

        // If the Merkle path length is not equal to `DEPTH`, pad the path with the empty hash.
        path.resize(DEPTH as usize, self.empty_hash);

        // Return the Merkle path.
        MerklePath::try_from((U64::new(leaf_index as u64), path))
    }

    /// Returns `true` if the given Merkle path is valid for the given root and leaf.
    pub fn verify(&self, path: &MerklePath<E, DEPTH>, root: &PH::Hash, leaf: &LH::Leaf) -> bool {
        path.verify(&self.leaf_hasher, &self.path_hasher, root, leaf)
    }

    /// Returns the Merkle root of the tree.
    pub const fn root(&self) -> &PH::Hash {
        &self.root
    }

    /// Returns the Merkle tree (excluding the hashes of the leaves).
    pub fn tree(&self) -> &[PH::Hash] {
        &self.tree
    }

    /// Returns the empty hash.
    pub const fn empty_hash(&self) -> &PH::Hash {
        &self.empty_hash
    }

    /// Returns the leaf hashes from the Merkle tree.
    pub fn leaf_hashes(&self) -> &[LH::Hash] {
        // Compute the start index (on the left) for the leaf hashes level in the Merkle tree.
        let start = self.number_of_leaves.next_power_of_two() - 1;
        // Compute the end index (on the right) for the leaf hashes level in the Merkle tree.
        let end = start + self.number_of_leaves;
        // Return the leaf hashes.
        &self.tree[start..end]
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

/// Returns true iff the index represents the root.
#[inline]
const fn is_root(index: usize) -> bool {
    index == 0
}

/// Returns true iff the given index represents a left child.
#[inline]
const fn is_left_child(index: usize) -> bool {
    index % 2 == 1
}

/// Returns the index of the parent, given the index of a child.
#[inline]
const fn parent(index: usize) -> Option<usize> {
    if index > 0 { Some((index - 1) >> 1) } else { None }
}
