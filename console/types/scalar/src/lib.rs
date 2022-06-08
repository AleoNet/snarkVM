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
mod compare;
mod from_bits;
mod one;
mod parse;
mod random;
mod size_in_bits;
mod to_bits;
mod zero;

pub use snarkvm_console_network::prelude::*;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Scalar<N: Network> {
    /// The underlying scalar element.
    scalar: N::Scalar,
}

impl<N: Network> ScalarTrait for Scalar<N> {}

impl<N: Network> Scalar<N> {
    /// Initializes a new scalar.
    pub const fn new(scalar: N::Scalar) -> Self {
        Self { scalar }
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
