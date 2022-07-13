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

impl FromBytes for LiteralType {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let index = u16::read_le(&mut reader)?;
        FromPrimitive::from_u16(index).ok_or_else(|| error("Failed to deserialize literal type variant {index}"))
    }
}

impl ToBytes for LiteralType {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (*self as u16).write_le(&mut writer)
    }
}
