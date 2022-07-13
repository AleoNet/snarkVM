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
mod parse;
mod random;
mod serialize;

pub use snarkvm_console_network_environment::prelude::*;
pub use snarkvm_console_types_boolean::Boolean;
pub use snarkvm_console_types_field::Field;
pub use snarkvm_console_types_integers::Integer;

use core::marker::PhantomData;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct StringType<E: Environment> {
    /// The underlying string.
    string: String,
    /// PhantomData
    _phantom: PhantomData<E>,
}

impl<E: Environment> StringTrait for StringType<E> {}

impl<E: Environment> StringType<E> {
    /// Initializes a new string.
    pub fn new(string: &str) -> Self {
        // Ensure the string is within the allowed capacity.
        let num_bytes = string.len();
        match num_bytes <= E::MAX_STRING_BYTES as usize {
            true => Self { string: string.to_string(), _phantom: PhantomData },
            false => E::halt(format!("Attempted to allocate a string of size {num_bytes}")),
        }
    }
}

impl<E: Environment> TypeName for StringType<E> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "string"
    }
}

impl<E: Environment> Deref for StringType<E> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.string.as_str()
    }
}
