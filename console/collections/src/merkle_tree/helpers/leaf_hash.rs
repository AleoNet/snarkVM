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

use snarkvm_console_algorithms::{Hash, Poseidon, BHP};
use snarkvm_curves::AffineCurve;

/// A trait for a Merkle leaf hash function.
pub trait LeafHash: Clone + Send + Sync {
    type Leaf: Clone + Send + Sync;
    type Hash: PrimeField;

    /// Returns the hash of the given leaf node.
    fn hash_leaf(&self, leaf: &Self::Leaf) -> Result<Self::Hash>;

    /// Returns the hash for each leaf node.
    fn hash_leaves(&self, leaves: &[Self::Leaf]) -> Result<Vec<Self::Hash>> {
        match leaves.len() {
            0 => Ok(vec![]),
            1..=100 => leaves.iter().map(|leaf| self.hash_leaf(leaf)).collect(),
            _ => cfg_iter!(leaves).map(|leaf| self.hash_leaf(leaf)).collect(),
        }
    }
}

impl<G: AffineCurve, const NUM_WINDOWS: u8, const WINDOW_SIZE: u8> LeafHash for BHP<G, NUM_WINDOWS, WINDOW_SIZE>
where
    G::BaseField: PrimeField,
{
    type Hash = G::BaseField;
    type Leaf = Vec<bool>;

    /// Returns the hash of the given leaf node.
    fn hash_leaf(&self, leaf: &Self::Leaf) -> Result<Self::Hash> {
        // Prepend the leaf with a `false` bit.
        let mut input = vec![false];
        input.extend(leaf);
        // Hash the input.
        Hash::hash(self, &input)
    }
}

impl<F: PrimeField, const RATE: usize> LeafHash for Poseidon<F, RATE> {
    type Hash = F;
    type Leaf = Vec<Self::Hash>;

    /// Returns the hash of the given leaf node.
    fn hash_leaf(&self, leaf: &Self::Leaf) -> Result<Self::Hash> {
        // Prepend the leaf with a `0field` element.
        let mut input = vec![Self::Hash::zero(); 1];
        input.extend(leaf);
        // Hash the input.
        Hash::hash(self, &input)
    }
}
