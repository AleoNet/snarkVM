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

mod bitwise;
mod bytes;
mod from_bits;
mod parse;
mod random;
mod serialize;
mod size_in_bits;
mod size_in_bytes;
mod to_bits;

pub use snarkvm_console_network_environment::prelude::*;

use core::marker::PhantomData;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Boolean<E: Environment> {
    /// The underlying boolean.
    boolean: bool,
    /// PhantomData.
    _phantom: PhantomData<E>,
}

impl<E: Environment> BooleanTrait for Boolean<E> {}

impl<E: Environment> Boolean<E> {
    /// Initializes a new boolean.
    pub const fn new(boolean: bool) -> Self {
        Self { boolean, _phantom: PhantomData }
    }

    /// Initializes a `false` boolean.
    #[deprecated(since = "0.1.0", note = "This is used for **testing** purposes")]
    pub const fn zero() -> Self {
        Self::new(false)
    }
}

impl<E: Environment> TypeName for Boolean<E> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "boolean"
    }
}

impl<E: Environment> Deref for Boolean<E> {
    type Target = bool;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.boolean
    }
}
