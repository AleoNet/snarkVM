// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use snarkvm_console_algorithms::{Keccak, Poseidon, BHP};
use snarkvm_console_types::prelude::*;

#[cfg(not(feature = "serial"))]
use rayon::prelude::*;

/// A trait for a Merkle path hash function.
pub trait PathHash: Clone + Send + Sync {
    type Hash: FieldTrait;

    /// Returns the empty hash.
    fn hash_empty<const ARITY: u8>(&self) -> Result<Self::Hash> {
        let children = (0..ARITY).map(|_| Self::Hash::zero()).collect::<Vec<_>>();
        self.hash_children(&children)
    }

    /// Returns the hash of the given child nodes.
    fn hash_children(&self, children: &[Self::Hash]) -> Result<Self::Hash>;

    /// Returns the hash for each tuple of child nodes.
    fn hash_all_children(&self, child_nodes: &[Vec<Self::Hash>]) -> Result<Vec<Self::Hash>> {
        match child_nodes.len() {
            0 => Ok(vec![]),
            1..=100 => child_nodes.iter().map(|children| self.hash_children(children)).collect(),
            _ => cfg_iter!(child_nodes).map(|children| self.hash_children(children)).collect(),
        }
    }
}

impl<E: Environment, const NUM_WINDOWS: u8, const WINDOW_SIZE: u8> PathHash for BHP<E, NUM_WINDOWS, WINDOW_SIZE> {
    type Hash = Field<E>;

    /// Returns the hash of the given child nodes.
    fn hash_children(&self, children: &[Self::Hash]) -> Result<Self::Hash> {
        // Prepend the nodes with a `true` bit.
        let mut input = vec![true];
        for child in children {
            child.write_bits_le(&mut input);
        }
        // Hash the input.
        Hash::hash(self, &input)
    }
}

impl<E: Environment, const RATE: usize> PathHash for Poseidon<E, RATE> {
    type Hash = Field<E>;

    /// Returns the hash of the given child nodes.
    fn hash_children(&self, children: &[Self::Hash]) -> Result<Self::Hash> {
        // Prepend the nodes with a `1field` byte.
        let mut input = vec![Self::Hash::one()];
        for child in children {
            input.push(*child);
        }
        // Hash the input.
        Hash::hash(self, &input)
    }
}

impl<const TYPE: u8, const VARIANT: usize> PathHash for Keccak<TYPE, VARIANT> {
    type Hash = Field<Console>;

    /// Returns the hash of the given child nodes.
    fn hash_children(&self, children: &[Self::Hash]) -> Result<Self::Hash> {
        // Prepend the nodes with a `true` bit.
        let mut input = vec![true];
        for child in children {
            child.write_bits_le(&mut input);
        }
        // Hash the input.
        let output = Hash::hash(self, &input)?;

        // TODO (raychu86): Use the generic `Hash` type to avoid this conversion.
        // Convert the bits to a field element, truncating if necessary.
        let bits: Vec<_> = output.iter().take(Self::Hash::size_in_data_bits()).copied().collect();
        Self::Hash::from_bits_le(&bits)
    }
}
