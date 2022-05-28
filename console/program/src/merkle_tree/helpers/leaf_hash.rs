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

/// A trait for a Merkle leaf hash function.
pub trait LeafHash<N: Network>: Clone + Send + Sync {
    type Leaf: Clone + Send + Sync;

    /// Returns the hash of the given leaf node.
    fn hash(&self, leaf: &Self::Leaf) -> Result<N::Field>;
}

impl<N: Network, const NUM_WINDOWS: u8, const WINDOW_SIZE: u8> LeafHash<N>
    for BHP<N::Affine, NUM_WINDOWS, WINDOW_SIZE>
{
    type Leaf = Vec<bool>;

    /// Returns the hash of the given leaf node.
    fn hash(&self, leaf: &Self::Leaf) -> Result<N::Field> {
        // Prepend the leaf with a `false` bit.
        let mut input = vec![false];
        input.extend(leaf);
        // Hash the input.
        Hash::hash(self, &input)
    }
}

impl<N: Network, const RATE: usize> LeafHash<N> for Poseidon<N::Field, RATE> {
    type Leaf = Vec<N::Field>;

    /// Returns the hash of the given leaf node.
    fn hash(&self, leaf: &Self::Leaf) -> Result<N::Field> {
        // Prepend the leaf with a `0field` element.
        let mut input = vec![N::Field::zero(); 1];
        input.extend(leaf);
        // Hash the input.
        Hash::hash(self, &input)
    }
}
