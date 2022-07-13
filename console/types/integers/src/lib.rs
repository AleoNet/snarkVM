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
mod from_field;
mod from_fields;
mod one;
mod parse;
mod random;
mod serialize;
mod size_in_bits;
mod size_in_bytes;
mod to_bits;
mod to_field;
mod to_fields;
mod zero;

pub use snarkvm_console_network_environment::prelude::*;
pub use snarkvm_console_types_boolean::Boolean;
pub use snarkvm_console_types_field::Field;

use snarkvm_console_network_environment::traits::integers::*;

use core::marker::PhantomData;

pub type I8<E> = Integer<E, i8>;
pub type I16<E> = Integer<E, i16>;
pub type I32<E> = Integer<E, i32>;
pub type I64<E> = Integer<E, i64>;
pub type I128<E> = Integer<E, i128>;

pub type U8<E> = Integer<E, u8>;
pub type U16<E> = Integer<E, u16>;
pub type U32<E> = Integer<E, u32>;
pub type U64<E> = Integer<E, u64>;
pub type U128<E> = Integer<E, u128>;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Integer<E: Environment, I: IntegerType> {
    /// The underlying integer value.
    integer: I,
    /// PhantomData.
    _phantom: PhantomData<E>,
}

impl<E: Environment, I: IntegerType> IntegerTrait<I, U8<E>, U16<E>, U32<E>> for Integer<E, I> {}

impl<E: Environment, I: IntegerType> IntegerCore<I> for Integer<E, I> {}

impl<E: Environment, I: IntegerType> Visibility for Integer<E, I> {
    /// Returns the number of field elements to encode `self`.
    fn size_in_fields(&self) -> Result<u16> {
        Ok(1)
    }
}

impl<E: Environment, I: IntegerType> Integer<E, I> {
    pub const MAX: Self = Self::new(I::MAX);
    pub const MIN: Self = Self::new(I::MIN);

    /// Initializes a new integer.
    pub const fn new(integer: I) -> Self {
        Self { integer, _phantom: PhantomData }
    }
}

impl<E: Environment, I: IntegerType> TypeName for Integer<E, I> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        I::type_name()
    }
}

impl<E: Environment, I: IntegerType> Deref for Integer<E, I> {
    type Target = I;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.integer
    }
}
