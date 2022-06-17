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

mod find;
mod num_randomizers;
mod parse;
mod to_bits;

use crate::{Ciphertext, Entry, Identifier, Plaintext, Record};
use snarkvm_console_network::Network;
use snarkvm_console_types::prelude::*;

/// A value stored in program data.
#[derive(Clone, PartialEq, Eq)]
pub enum Value<N: Network, Private: Visibility> {
    /// A constant value.
    Constant(Plaintext<N>),
    /// A publicly-visible value.
    Public(Plaintext<N>),
    /// A private value encrypted under the address of the record owner.
    Private(Private),
    /// A record value inherits its visibility from its record definition.
    Record(Record<N, Private>),
}

impl<N: Network, Private: Visibility> From<Entry<N, Private>> for Value<N, Private> {
    fn from(entry: Entry<N, Private>) -> Self {
        match entry {
            Entry::Constant(plaintext) => Value::Constant(plaintext),
            Entry::Public(plaintext) => Value::Public(plaintext),
            Entry::Private(private) => Value::Private(private),
        }
    }
}
