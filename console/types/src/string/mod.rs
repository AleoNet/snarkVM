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

mod parse;

use snarkvm_console_network::prelude::*;

use core::marker::PhantomData;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct StringType<N: Network> {
    /// The underlying string.
    string: String,
    /// The input mode for the string.
    mode: Mode,
    /// PhantomData
    _phantom: PhantomData<N>,
}

impl<N: Network> StringTrait for StringType<N> {}

impl<N: Network> StringType<N> {
    /// Initializes a new string with the given mode.
    pub fn new(mode: Mode, string: &str) -> Self {
        // Ensure the string is within the allowed capacity.
        let num_bytes = string.len();
        match num_bytes <= N::MAX_STRING_BYTES as usize {
            true => Self { string: string.to_string(), mode, _phantom: PhantomData },
            false => N::halt(format!("Attempted to allocate a string of size {num_bytes}")),
        }
    }

    /// Returns the mode of the string element.
    pub const fn mode(&self) -> Mode {
        self.mode
    }
}

impl<N: Network> TypeName for StringType<N> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "string"
    }
}

impl<N: Network> Deref for StringType<N> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.string.as_str()
    }
}
