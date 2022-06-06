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

mod arithmetic;
// mod one;
mod parse;
mod zero;

use crate::Scalar;
use snarkvm_console_network::prelude::*;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Group<N: Network> {
    /// The underlying group element.
    group: N::Projective,
    /// The input mode for the group element.
    mode: Mode,
}

impl<N: Network> GroupTrait<Scalar<N>> for Group<N> {}

impl<N: Network> Group<N> {
    /// Initializes a new group with the given mode.
    pub fn new(mode: Mode, group: N::Affine) -> Self {
        Self { group: group.into(), mode }
    }

    /// Returns the mode of the group element.
    pub const fn mode(&self) -> Mode {
        self.mode
    }
}

impl<N: Network> Group<N> {
    /// This internal function initializes a group element from projective coordinates.
    const fn from_projective(mode: Mode, group: N::Projective) -> Self {
        Self { group, mode }
    }
}

impl<N: Network> TypeName for Group<N> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "group"
    }
}
