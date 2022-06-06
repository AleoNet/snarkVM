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
mod one;
mod parse;
mod zero;

use snarkvm_console_network::prelude::*;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Scalar<N: Network> {
    /// The underlying scalar element.
    scalar: N::Scalar,
    /// The input mode for the scalar element.
    mode: Mode,
}

impl<N: Network> ScalarTrait for Scalar<N> {}

impl<N: Network> Scalar<N> {
    /// Initializes a new scalar with the given mode.
    pub const fn new(mode: Mode, scalar: N::Scalar) -> Self {
        Self { scalar, mode }
    }

    /// Returns the mode of the scalar element.
    pub const fn mode(&self) -> Mode {
        self.mode
    }
}

impl<N: Network> TypeName for Scalar<N> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "scalar"
    }
}

impl<N: Network> Deref for Scalar<N> {
    type Target = N::Scalar;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.scalar
    }
}
