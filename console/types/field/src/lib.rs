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

pub use snarkvm_console_network_environment::prelude::*;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Field<E: Environment> {
    /// The underlying field element.
    field: E::Field,
}

impl<E: Environment> FieldTrait for Field<E> {}

impl<E: Environment> Field<E> {
    /// Initializes a new field.
    pub const fn new(field: E::Field) -> Self {
        Self { field }
    }
}

impl<E: Environment> TypeName for Field<E> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "field"
    }
}

impl<E: Environment> Deref for Field<E> {
    type Target = E::Field;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.field
    }
}
