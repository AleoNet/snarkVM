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
mod one;
mod parse;
mod zero;

use snarkvm_console_network::{prelude::*, traits::integers::*};

use core::marker::PhantomData;

pub type I8<N> = Integer<N, i8>;
pub type I16<N> = Integer<N, i16>;
pub type I32<N> = Integer<N, i32>;
pub type I64<N> = Integer<N, i64>;
pub type I128<N> = Integer<N, i128>;

pub type U8<N> = Integer<N, u8>;
pub type U16<N> = Integer<N, u16>;
pub type U32<N> = Integer<N, u32>;
pub type U64<N> = Integer<N, u64>;
pub type U128<N> = Integer<N, u128>;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Integer<N: Network, I: IntegerType> {
    /// The underlying integer value.
    integer: I,
    /// PhantomData.
    _phantom: PhantomData<N>,
}

impl<N: Network, I: IntegerType> IntegerTrait<I, U8<N>, U16<N>, U32<N>> for Integer<N, I> {}

impl<N: Network, I: IntegerType> IntegerCore<I> for Integer<N, I> {}

impl<N: Network, I: IntegerType> Integer<N, I> {
    /// Initializes a new integer.
    pub const fn new(integer: I) -> Self {
        Self { integer, _phantom: PhantomData }
    }
}

impl<N: Network, I: IntegerType> TypeName for Integer<N, I> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        I::type_name()
    }
}

impl<N: Network, I: IntegerType> Deref for Integer<N, I> {
    type Target = I;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.integer
    }
}
