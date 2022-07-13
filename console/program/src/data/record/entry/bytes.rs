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

use super::*;

impl<N: Network, Private: Visibility> FromBytes for Entry<N, Private> {
    /// Reads the entry from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the index.
        let index = u8::read_le(&mut reader)?;
        // Read the entry.
        let entry = match index {
            0 => Self::Constant(Plaintext::read_le(&mut reader)?),
            1 => Self::Public(Plaintext::read_le(&mut reader)?),
            2 => Self::Private(Private::read_le(&mut reader)?),
            3.. => return Err(error(format!("Failed to decode entry variant {index}"))),
        };
        Ok(entry)
    }
}

impl<N: Network, Private: Visibility> ToBytes for Entry<N, Private> {
    /// Writes the entry to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::Constant(plaintext) => {
                0u8.write_le(&mut writer)?;
                plaintext.write_le(&mut writer)
            }
            Self::Public(plaintext) => {
                1u8.write_le(&mut writer)?;
                plaintext.write_le(&mut writer)
            }
            Self::Private(private) => {
                2u8.write_le(&mut writer)?;
                private.write_le(&mut writer)
            }
        }
    }
}
