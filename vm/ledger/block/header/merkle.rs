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

/// The depth of the Merkle tree for the block header.
const HEADER_DEPTH: u8 = 3;

/// The Merkle tree for the block header.
type HeaderTree<N> = BHPMerkleTree<N, HEADER_DEPTH>;
/// The Merkle path for the block header.
pub type HeaderPath<N> = MerklePath<N, HEADER_DEPTH>;

impl<N: Network> Header<N> {
    /// Returns the block header root.
    pub fn to_root(&self) -> Result<Field<N>> {
        Ok(*self.to_tree()?.root())
    }

    /// Returns the Merkle path for the Merkle tree of the block header.
    pub fn to_path(&self, leaf: &HeaderLeaf<N>) -> Result<HeaderPath<N>> {
        // Compute the Merkle path.
        self.to_tree()?.prove(leaf.index() as usize, &leaf.to_bits_le())
    }

    /// Returns an instance of the Merkle tree for the block header.
    #[allow(clippy::useless_vec)]
    pub fn to_tree(&self) -> Result<HeaderTree<N>> {
        // Construct the metadata leaf (the last leaf in the Merkle tree).
        let metadata = self.metadata.to_bits_le(); // 304 bits
        // Ensure the metadata leaf is the correct size.
        ensure!(metadata.len() == 304, "Incorrect block header metadata size");

        // Determine the number of leaves.
        let num_leaves = usize::pow(2, HEADER_DEPTH as u32);

        // Construct the Merkle leaves.
        let mut leaves: Vec<Vec<bool>> = Vec::with_capacity(num_leaves);
        leaves.push(self.previous_state_root.to_bits_le());
        leaves.push(self.transactions_root.to_bits_le());
        leaves.extend_from_slice(&vec![vec![false; 256]; 5]);
        leaves.push(metadata);
        // Ensure the correct number of leaves are allocated.
        ensure!(num_leaves == leaves.len(), "Incorrect number of leaves in the Merkle tree for the block header");

        // Compute the Merkle tree.
        N::merkle_tree_bhp::<HEADER_DEPTH>(&leaves)
    }
}
