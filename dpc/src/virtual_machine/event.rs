// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::{Network, Operation};
use snarkvm_utilities::{FromBytes, ToBytes};

use std::io::{Read, Result as IoResult, Write};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Event<N: Network> {
    /// Emits publicly-visible arbitrary data.
    Custom(Vec<u8>),
    /// Emits the view key for an output record at the specified index in a transition.
    RecordViewKey(u8, Vec<u8>),
    /// Emits the operation performed in a transition.
    Operation(Operation<N>),
}

impl<N: Network> Event<N> {
    /// Returns the event ID.
    #[inline]
    fn id(&self) -> u8 {
        match self {
            Self::Custom(..) => 0,
            Self::RecordViewKey(..) => 1,
            Self::Operation(..) => 2,
        }
    }
}

impl<N: Network> FromBytes for Event<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let id: u8 = FromBytes::read_le(&mut reader)?;
        match id {
            0 => {
                let num_bytes: u16 = FromBytes::read_le(&mut reader)?;
                let mut buffer = vec![0u8; num_bytes as usize];
                reader.read_exact(&mut buffer)?;
                Ok(Self::Custom(buffer))
            }
            1 => {
                let index: u8 = FromBytes::read_le(&mut reader)?;
                let mut record_view_key = vec![0u8; 32];
                reader.read_exact(&mut record_view_key)?;
                Ok(Self::RecordViewKey(index, record_view_key))
            }
            2 => Ok(Self::Operation(FromBytes::read_le(&mut reader)?)),
            _ => unreachable!("Invalid event ID during deserialization"),
        }
    }
}

impl<N: Network> ToBytes for Event<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.id().write_le(&mut writer)?;
        match self {
            Self::Custom(buffer) => {
                (buffer.len() as u16).write_le(&mut writer)?;
                buffer.write_le(&mut writer)
            }
            Self::RecordViewKey(index, record_view_key) => {
                index.write_le(&mut writer)?;
                record_view_key.write_le(&mut writer)
            }
            Self::Operation(operation) => operation.write_le(&mut writer),
        }
    }
}
