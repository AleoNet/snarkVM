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

use snarkvm_console_algorithms::{Poseidon, BHP};
use snarkvm_console_types::prelude::*;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// A trait for a Merkle path hash function.
pub trait PathHash: Clone + Send + Sync {
    type Hash: FieldTrait;

    /// Returns the empty hash.
    fn hash_empty(&self) -> Result<Self::Hash> {
        self.hash_children(&Self::Hash::zero(), &Self::Hash::zero())
    }

    /// Returns the hash of the given child nodes.
    fn hash_children(&self, left: &Self::Hash, right: &Self::Hash) -> Result<Self::Hash>;

    /// Returns the hash for each tuple of child nodes.
    fn hash_all_children(&self, child_nodes: &[(Self::Hash, Self::Hash)]) -> Result<Vec<Self::Hash>> {
        match child_nodes.len() {
            0 => Ok(vec![]),
            1..=100 => child_nodes.iter().map(|(left, right)| self.hash_children(left, right)).collect(),
            _ => cfg_iter!(child_nodes).map(|(left, right)| self.hash_children(left, right)).collect(),
        }
    }
}

impl<E: Environment, const NUM_WINDOWS: u8, const WINDOW_SIZE: u8> PathHash for BHP<E, NUM_WINDOWS, WINDOW_SIZE> {
    type Hash = Field<E>;

    /// Returns the hash of the given child nodes.
    fn hash_children(&self, left: &Self::Hash, right: &Self::Hash) -> Result<Self::Hash> {
        // Prepend the nodes with a `true` bit.
        let mut input = vec![true];
        input.extend(left.to_bits_le());
        input.extend(right.to_bits_le());
        // Hash the input.
        Hash::hash(self, &input)
    }
}

impl<E: Environment, const RATE: usize> PathHash for Poseidon<E, RATE> {
    type Hash = Field<E>;

    /// Returns the hash of the given child nodes.
    fn hash_children(&self, left: &Self::Hash, right: &Self::Hash) -> Result<Self::Hash> {
        // Prepend the nodes with a `1field` byte.
        let mut input = vec![Self::Hash::one()];
        input.push(*left);
        input.push(*right);
        // Hash the input.
        Hash::hash(self, &input)
    }
}
