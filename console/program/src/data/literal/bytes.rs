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

impl<N: Network> FromBytes for Literal<N> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let index = u16::read_le(&mut reader)?;
        let literal = match index {
            0 => Self::Address(Address::read_le(&mut reader)?),
            1 => Self::Boolean(Boolean::read_le(&mut reader)?),
            2 => Self::Field(Field::read_le(&mut reader)?),
            3 => Self::Group(Group::read_le(&mut reader)?),
            4 => Self::I8(I8::read_le(&mut reader)?),
            5 => Self::I16(I16::read_le(&mut reader)?),
            6 => Self::I32(I32::read_le(&mut reader)?),
            7 => Self::I64(I64::read_le(&mut reader)?),
            8 => Self::I128(I128::read_le(&mut reader)?),
            9 => Self::U8(U8::read_le(&mut reader)?),
            10 => Self::U16(U16::read_le(&mut reader)?),
            11 => Self::U32(U32::read_le(&mut reader)?),
            12 => Self::U64(U64::read_le(&mut reader)?),
            13 => Self::U128(U128::read_le(&mut reader)?),
            14 => Self::Scalar(Scalar::read_le(&mut reader)?),
            15 => Self::String(StringType::read_le(&mut reader)?),
            16.. => return Err(error(format!("Failed to deserialize literal variant {index}"))),
        };
        Ok(literal)
    }
}

impl<N: Network> ToBytes for Literal<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (self.enum_index() as u16).write_le(&mut writer)?;
        match self {
            Self::Address(primitive) => primitive.write_le(&mut writer),
            Self::Boolean(primitive) => primitive.write_le(&mut writer),
            Self::Field(primitive) => primitive.write_le(&mut writer),
            Self::Group(primitive) => primitive.write_le(&mut writer),
            Self::I8(primitive) => primitive.write_le(&mut writer),
            Self::I16(primitive) => primitive.write_le(&mut writer),
            Self::I32(primitive) => primitive.write_le(&mut writer),
            Self::I64(primitive) => primitive.write_le(&mut writer),
            Self::I128(primitive) => primitive.write_le(&mut writer),
            Self::U8(primitive) => primitive.write_le(&mut writer),
            Self::U16(primitive) => primitive.write_le(&mut writer),
            Self::U32(primitive) => primitive.write_le(&mut writer),
            Self::U64(primitive) => primitive.write_le(&mut writer),
            Self::U128(primitive) => primitive.write_le(&mut writer),
            Self::Scalar(primitive) => primitive.write_le(&mut writer),
            Self::String(primitive) => primitive.write_le(&mut writer),
        }
    }
}
