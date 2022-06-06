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

use crate::ValueType;
use snarkvm_console_network::prelude::*;
use snarkvm_utilities::{
    error,
    io::{Read, Result as IoResult, Write},
    FromBytes,
    ToBytes,
};

use enum_index::EnumIndex;

#[derive(Copy, Clone, PartialEq, Eq, Hash, EnumIndex)]
pub enum Entry<N: Network> {
    /// A constant value.
    Constant(ValueType<N>),
    /// A publicly-visible value.
    Public(ValueType<N>),
    /// A private value decrypted with the account owner's address.
    Private(ValueType<N>),
}

impl<N: Network> ToBytes for Entry<N> {
    /// Writes an entry to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (self.enum_index() as u8).write_le(&mut writer)?;
        match self {
            Entry::Constant(value_type) => value_type.write_le(&mut writer),
            Entry::Public(value_type) => value_type.write_le(&mut writer),
            Entry::Private(value_type) => value_type.write_le(&mut writer),
        }
    }
}

impl<N: Network> FromBytes for Entry<N> {
    /// Reads an entry from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let variant = u8::read_le(&mut reader)?;
        match variant {
            0 => Ok(Entry::Constant(ValueType::read_le(&mut reader)?)),
            1 => Ok(Entry::Public(ValueType::read_le(&mut reader)?)),
            2 => Ok(Entry::Private(ValueType::read_le(&mut reader)?)),
            _ => Err(error(format!("Failed to deserialize entry variant {}", variant))),
        }
    }
}
