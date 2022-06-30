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

mod sponge;
pub(super) use sponge::*;

mod state;
pub(super) use state::*;

use snarkvm_console_types::{prelude::*, Field};

use smallvec::SmallVec;

/// The interface for a cryptographic sponge.
/// A sponge can `absorb` or take in inputs and later `squeeze` or output bytes or field elements.
/// The outputs are dependent on previous `absorb` and `squeeze` calls.
pub trait AlgebraicSponge<E: Environment, const RATE: usize, const CAPACITY: usize>: Clone + Debug {
    /// Parameters used by the sponge.
    type Parameters;

    /// Initialize a new instance of the sponge.
    fn new(params: &Self::Parameters) -> Self;

    /// Absorb an input into the sponge.
    fn absorb(&mut self, input: &[Field<E>]);

    /// Squeeze `num_elements` field elements from the sponge.
    fn squeeze(&mut self, num_elements: u16) -> SmallVec<[Field<E>; 10]>;
}

/// The mode structure for duplex sponges.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum DuplexSpongeMode {
    /// The sponge is currently absorbing data.
    Absorbing {
        /// The next position of the state to be XOR-ed when absorbing.
        next_absorb_index: usize,
    },
    /// The sponge is currently squeezing data out.
    Squeezing {
        /// The next position of the state to be outputted when squeezing.
        next_squeeze_index: usize,
    },
}
