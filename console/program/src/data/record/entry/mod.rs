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

mod bytes;
mod find;
mod num_randomizers;
mod parse;
mod to_bits;

use crate::{Ciphertext, Identifier, Literal, Plaintext};
use snarkvm_console_network::Network;
use snarkvm_console_types::prelude::*;

use indexmap::IndexMap;

/// An entry stored in program data.
#[derive(Clone, PartialEq, Eq)]
pub enum Entry<N: Network, Private: Visibility> {
    /// A constant entry.
    Constant(Plaintext<N>),
    /// A publicly-visible entry.
    Public(Plaintext<N>),
    /// A private entry encrypted under the address of the record owner.
    Private(Private),
}
