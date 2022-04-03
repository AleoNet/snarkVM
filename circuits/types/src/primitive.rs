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

use crate::prelude::*;
use snarkvm_utilities::{
    error,
    io::{Read, Result as IoResult, Write},
    FromBytes,
    ToBytes,
};

use enum_index::EnumIndex;

#[derive(Debug, PartialEq, Eq, Hash, EnumIndex)]
pub enum Primitive<E: Environment> {
    /// The Aleo address type.
    Address(<Address<E> as Eject>::Primitive),
    /// The boolean type.
    Boolean(<Boolean<E> as Eject>::Primitive),
    /// The field type (base field).
    Field(<Field<E> as Eject>::Primitive),
    /// The group type (affine).
    Group(<Group<E> as Eject>::Primitive),
    /// The 8-bit signed integer type.
    I8(<I8<E> as Eject>::Primitive),
    /// The 16-bit signed integer type.
    I16(<I16<E> as Eject>::Primitive),
    /// The 32-bit signed integer type.
    I32(<I32<E> as Eject>::Primitive),
    /// The 64-bit signed integer type.
    I64(<I64<E> as Eject>::Primitive),
    /// The 128-bit signed integer type.
    I128(<I128<E> as Eject>::Primitive),
    /// The 8-bit unsigned integer type.
    U8(<U8<E> as Eject>::Primitive),
    /// The 16-bit unsigned integer type.
    U16(<U16<E> as Eject>::Primitive),
    /// The 32-bit unsigned integer type.
    U32(<U32<E> as Eject>::Primitive),
    /// The 64-bit unsigned integer type.
    U64(<U64<E> as Eject>::Primitive),
    /// The 128-bit unsigned integer type.
    U128(<U128<E> as Eject>::Primitive),
    /// The scalar type (scalar field).
    Scalar(<Scalar<E> as Eject>::Primitive),
    /// The string type.
    String(<StringType<E> as Eject>::Primitive),
}

impl<E: Environment> Default for Primitive<E> {
    fn default() -> Self {
        Primitive::Field(Default::default())
    }
}

impl<E: Environment> FromBytes for Primitive<E> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let index = u16::read_le(&mut reader)?;
        let literal = match index {
            0 => Self::Address(FromBytes::read_le(&mut reader)?),
            1 => Self::Boolean(FromBytes::read_le(&mut reader)?),
            2 => Self::Field(FromBytes::read_le(&mut reader)?),
            3 => Self::Group(FromBytes::read_le(&mut reader)?),
            4 => Self::I8(FromBytes::read_le(&mut reader)?),
            5 => Self::I16(FromBytes::read_le(&mut reader)?),
            6 => Self::I32(FromBytes::read_le(&mut reader)?),
            7 => Self::I64(FromBytes::read_le(&mut reader)?),
            8 => Self::I128(FromBytes::read_le(&mut reader)?),
            9 => Self::U8(FromBytes::read_le(&mut reader)?),
            10 => Self::U16(FromBytes::read_le(&mut reader)?),
            11 => Self::U32(FromBytes::read_le(&mut reader)?),
            12 => Self::U64(FromBytes::read_le(&mut reader)?),
            13 => Self::U128(FromBytes::read_le(&mut reader)?),
            14 => Self::Scalar(FromBytes::read_le(&mut reader)?),
            15 => {
                let size = u32::read_le(&mut reader)?;
                let mut buffer = vec![0u8; size as usize];
                reader.read_exact(&mut buffer)?;
                Self::String(String::from_utf8(buffer).map_err(|e| error(format!("{e}")))?)
            }
            16.. => return Err(error(format!("Failed to deserialize primitive variant {index}"))),
        };
        Ok(literal)
    }
}

impl<E: Environment> ToBytes for Primitive<E> {
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
            Self::String(primitive) => {
                (primitive.as_bytes().len() as u32).write_le(&mut writer)?;
                primitive.as_bytes().write_le(&mut writer)
            }
        }
    }
}
