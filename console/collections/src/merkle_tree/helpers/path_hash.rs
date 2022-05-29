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

/// A trait for a Merkle path hash function.
pub trait PathHash<N: Network>: Clone + Send + Sync {
    /// Returns the hash of the given child nodes.
    fn hash_children(&self, left: &N::Field, right: &N::Field) -> Result<N::Field>;

    /// Returns the empty hash.
    fn hash_empty(&self) -> Result<N::Field> {
        self.hash_children(&N::Field::zero(), &N::Field::zero())
    }

    /// Returns the hash for each tuple of child nodes.
    fn hash_all_children(&self, child_nodes: &[(N::Field, N::Field)]) -> Result<Vec<N::Field>> {
        match child_nodes.len() {
            0 => Ok(vec![]),
            1..=100 => child_nodes.iter().map(|(left, right)| self.hash_children(left, right)).collect(),
            _ => cfg_iter!(child_nodes).map(|(left, right)| self.hash_children(left, right)).collect(),
        }
    }
}

impl<N: Network, const NUM_WINDOWS: u8, const WINDOW_SIZE: u8> PathHash<N>
    for BHP<N::Affine, NUM_WINDOWS, WINDOW_SIZE>
{
    /// Returns the hash of the given child nodes.
    fn hash_children(&self, left: &N::Field, right: &N::Field) -> Result<N::Field> {
        // Prepend the nodes with a `true` bit.
        let mut input = vec![true];
        input.extend(left.to_bits_le());
        input.extend(right.to_bits_le());
        // Hash the input.
        Hash::hash(self, &input)
    }
}

impl<N: Network, const RATE: usize> PathHash<N> for Poseidon<N::Field, RATE> {
    /// Returns the hash of the given child nodes.
    fn hash_children(&self, left: &N::Field, right: &N::Field) -> Result<N::Field> {
        // Prepend the nodes with a `1field` byte.
        let mut input = vec![N::Field::one()];
        input.push(*left);
        input.push(*right);
        // Hash the input.
        Hash::hash(self, &input)
    }
}
