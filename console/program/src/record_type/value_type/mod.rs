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
mod parse;

use crate::PlaintextType;
use snarkvm_console_network::prelude::*;
use snarkvm_utilities::{
    error,
    io::{Read, Result as IoResult, Write},
    FromBytes,
    ToBytes,
};

use enum_index::EnumIndex;

#[derive(Copy, Clone, PartialEq, Eq, Hash, EnumIndex)]
pub enum ValueType<N: Network> {
    /// A constant value.
    Constant(PlaintextType<N>),
    /// A publicly-visible value.
    Public(PlaintextType<N>),
    /// A private value decrypted with the account owner's address.
    Private(PlaintextType<N>),
}

impl<N: Network> ValueType<N> {
    /// Returns the value type as a plaintext type.
    #[inline]
    pub fn to_plaintext_type(&self) -> PlaintextType<N> {
        match self {
            ValueType::Constant(plaintext_type) => *plaintext_type,
            ValueType::Public(plaintext_type) => *plaintext_type,
            ValueType::Private(plaintext_type) => *plaintext_type,
        }
    }
}
