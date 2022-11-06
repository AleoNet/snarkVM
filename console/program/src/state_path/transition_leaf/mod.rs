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

use snarkvm_console_network::prelude::*;
use snarkvm_console_types::Field;

const VERSION: u8 = 0u8;

/// The Merkle leaf for an input or output ID in the transition.
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct TransitionLeaf<N: Network> {
    /// The version of the Merkle leaf.
    version: u8,
    /// The index of the Merkle leaf.
    index: u8,
    /// The variant of the Merkle leaf.
    variant: u16,
    /// The ID.
    id: Field<N>,
}

impl<N: Network> TransitionLeaf<N> {
    /// Initializes a new instance of `TransitionLeaf`.
    pub const fn new_with_version(index: u8, variant: u16, id: Field<N>) -> Self {
        Self { version: VERSION, index, variant, id }
    }

    /// Initializes a new instance of `TransitionLeaf`.
    pub const fn from(version: u8, index: u8, variant: u16, id: Field<N>) -> Self {
        Self { version, index, variant, id }
    }

    /// Returns the version of the Merkle leaf.
    pub const fn version(&self) -> u8 {
        self.version
    }

    /// Returns the index of the Merkle leaf.
    pub const fn index(&self) -> u8 {
        self.index
    }

    /// Returns the variant of the Merkle leaf.
    pub const fn variant(&self) -> u16 {
        self.variant
    }

    /// Returns the ID in the Merkle leaf.
    pub const fn id(&self) -> Field<N> {
        self.id
    }
}

#[cfg(test)]
mod test_helpers {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    pub(super) fn sample_leaf(rng: &mut TestRng) -> TransitionLeaf<CurrentNetwork> {
        // Construct a new leaf.
        TransitionLeaf::new_with_version(rng.gen(), rng.gen(), Uniform::rand(rng))
    }
}
