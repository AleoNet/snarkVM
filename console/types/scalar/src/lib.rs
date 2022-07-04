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
mod bitwise;
mod bytes;
mod compare;
mod from_bits;
mod one;
mod parse;
mod random;
mod serialize;
mod size_in_bits;
mod size_in_bytes;
mod to_bits;
mod to_field;
mod zero;

pub use snarkvm_console_network_environment::prelude::*;
pub use snarkvm_console_types_boolean::Boolean;
pub use snarkvm_console_types_field::Field;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Scalar<E: Environment> {
    /// The underlying scalar element.
    scalar: E::Scalar,
}

impl<E: Environment> ScalarTrait for Scalar<E> {}

impl<E: Environment> Scalar<E> {
    /// The scalar size in bits.
    pub const SIZE_IN_BITS: usize = E::Scalar::SIZE_IN_BITS;
    /// The scalar size in bytes.
    pub const SIZE_IN_BYTES: usize = (E::Scalar::SIZE_IN_BITS + 7) / 8;
    /// The scalar capacity for data bits.
    pub const SIZE_IN_DATA_BITS: usize = E::Scalar::SIZE_IN_DATA_BITS;

    /// Initializes a new scalar.
    pub const fn new(scalar: E::Scalar) -> Self {
        Self { scalar }
    }
}

impl<E: Environment> TypeName for Scalar<E> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "scalar"
    }
}

impl<E: Environment> Deref for Scalar<E> {
    type Target = E::Scalar;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.scalar
    }
}
