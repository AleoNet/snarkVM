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

mod bytes;
mod serialize;
mod string;
mod to_bits;

use crate::console::{network::prelude::*, types::Field};

/// The Merkle leaf for the block header.
#[derive(Clone, PartialEq, Eq)]
pub struct HeaderLeaf<N: Network> {
    /// The index of the Merkle leaf.
    index: u8,
    /// The ID.
    id: Field<N>,
}

impl<N: Network> HeaderLeaf<N> {
    /// Initializes a new instance of `HeaderLeaf`.
    pub const fn new(index: u8, id: Field<N>) -> Self {
        Self { index, id }
    }

    /// Returns the index of the Merkle leaf.
    pub const fn index(&self) -> u8 {
        self.index
    }

    /// Returns the ID in the Merkle leaf.
    pub const fn id(&self) -> Field<N> {
        self.id
    }
}

#[cfg(test)]
mod test_helpers {
    use super::*;
    use crate::console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    pub(super) fn sample_leaf() -> HeaderLeaf<CurrentNetwork> {
        // Initialize an RNG.
        let rng = &mut test_crypto_rng();
        // Construct a new leaf.
        HeaderLeaf::new(rng.gen(), Uniform::rand(rng))
    }
}
