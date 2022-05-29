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

/// A trait for a Merkle path hash function.
pub trait PathHash<F: PrimeField>: Clone + Send + Sync {
    /// Returns the hash of the given child nodes.
    fn hash_children(&self, left: &F, right: &F) -> Result<F>;

    /// Returns the empty hash.
    fn hash_empty(&self) -> Result<F> {
        self.hash_children(&F::zero(), &F::zero())
    }

    /// Returns the hash for each tuple of child nodes.
    fn hash_all_children(&self, child_nodes: &[(F, F)]) -> Result<Vec<F>> {
        match child_nodes.len() {
            0 => Ok(vec![]),
            1..=100 => child_nodes.iter().map(|(left, right)| self.hash_children(left, right)).collect(),
            _ => cfg_iter!(child_nodes).map(|(left, right)| self.hash_children(left, right)).collect(),
        }
    }
}

impl<G: AffineCurve<BaseField = F>, F: PrimeField, const NUM_WINDOWS: u8, const WINDOW_SIZE: u8> PathHash<F>
    for BHP<G, NUM_WINDOWS, WINDOW_SIZE>
{
    /// Returns the hash of the given child nodes.
    fn hash_children(&self, left: &F, right: &F) -> Result<F> {
        // Prepend the nodes with a `true` bit.
        let mut input = vec![true];
        input.extend(left.to_bits_le());
        input.extend(right.to_bits_le());
        // Hash the input.
        Hash::hash(self, &input)
    }
}

impl<F: PrimeField, const RATE: usize> PathHash<F> for Poseidon<F, RATE> {
    /// Returns the hash of the given child nodes.
    fn hash_children(&self, left: &F, right: &F) -> Result<F> {
        // Prepend the nodes with a `1field` byte.
        let mut input = vec![F::one()];
        input.push(*left);
        input.push(*right);
        // Hash the input.
        Hash::hash(self, &input)
    }
}
