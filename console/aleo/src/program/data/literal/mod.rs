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

mod from_bits;
mod size_in_bits;
mod to_bits;
mod variant;

use crate::Address;
use snarkvm_console_network::Network;
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{
    error,
    io::{Read, Result as IoResult, Write},
    FromBits,
    FromBytes,
    ToBits,
    ToBytes,
};

use anyhow::{bail, Result};
use enum_index::EnumIndex;

/// The literal enum represents all supported types in snarkVM.
#[derive(Clone, Debug, PartialEq, Eq, Hash, EnumIndex)]
pub enum Literal<N: Network> {
    /// The Aleo address type.
    Address(Address<N>),
    /// The boolean type.
    Boolean(bool),
    /// The field type (base field).
    Field(N::Field),
    /// The group type (affine).
    Group(N::Affine),
    /// The 8-bit signed integer type.
    I8(i8),
    /// The 16-bit signed integer type.
    I16(i16),
    /// The 32-bit signed integer type.
    I32(i32),
    /// The 64-bit signed integer type.
    I64(i64),
    /// The 128-bit signed integer type.
    I128(i128),
    /// The 8-bit unsigned integer type.
    U8(u8),
    /// The 16-bit unsigned integer type.
    U16(u16),
    /// The 32-bit unsigned integer type.
    U32(u32),
    /// The 64-bit unsigned integer type.
    U64(u64),
    /// The 128-bit unsigned integer type.
    U128(u128),
    /// The scalar type (scalar field).
    Scalar(N::Scalar),
    /// The string type.
    String(String),
}

impl<N: Network> FromBytes for Literal<N> {
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
                if size > N::NUM_STRING_BYTES {
                    return Err(error(format!(
                        "String literal exceeds maximum length of {} bytes.",
                        N::NUM_STRING_BYTES
                    )));
                }
                let mut buffer = vec![0u8; size as usize];
                reader.read_exact(&mut buffer)?;
                Self::String(String::from_utf8(buffer).map_err(|e| error(format!("{e}")))?)
            }
            16.. => return Err(error(format!("Failed to deserialize primitive variant {index}"))),
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
            Self::String(primitive) => {
                (primitive.as_bytes().len() as u32).write_le(&mut writer)?;
                primitive.as_bytes().write_le(&mut writer)
            }
        }
    }
}

// impl<N: Network> Debug for Literal<N> {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         match self {
//             Self::Address(literal) => Debug::fmt(literal, f),
//             Self::Boolean(literal) => Debug::fmt(literal, f),
//             Self::Field(literal) => Debug::fmt(literal, f),
//             Self::Group(literal) => Debug::fmt(literal, f),
//             Self::I8(literal) => Debug::fmt(literal, f),
//             Self::I16(literal) => Debug::fmt(literal, f),
//             Self::I32(literal) => Debug::fmt(literal, f),
//             Self::I64(literal) => Debug::fmt(literal, f),
//             Self::I128(literal) => Debug::fmt(literal, f),
//             Self::U8(literal) => Debug::fmt(literal, f),
//             Self::U16(literal) => Debug::fmt(literal, f),
//             Self::U32(literal) => Debug::fmt(literal, f),
//             Self::U64(literal) => Debug::fmt(literal, f),
//             Self::U128(literal) => Debug::fmt(literal, f),
//             Self::Scalar(literal) => Debug::fmt(literal, f),
//             Self::String(literal) => Debug::fmt(literal, f),
//         }
//     }
// }
//
// impl<N: Network> Display for Literal<N> {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         match self {
//             Self::Address(literal) => Display::fmt(literal, f),
//             Self::Boolean(literal) => Display::fmt(literal, f),
//             Self::Field(literal) => Display::fmt(literal, f),
//             Self::Group(literal) => Display::fmt(literal, f),
//             Self::I8(literal) => Display::fmt(literal, f),
//             Self::I16(literal) => Display::fmt(literal, f),
//             Self::I32(literal) => Display::fmt(literal, f),
//             Self::I64(literal) => Display::fmt(literal, f),
//             Self::I128(literal) => Display::fmt(literal, f),
//             Self::U8(literal) => Display::fmt(literal, f),
//             Self::U16(literal) => Display::fmt(literal, f),
//             Self::U32(literal) => Display::fmt(literal, f),
//             Self::U64(literal) => Display::fmt(literal, f),
//             Self::U128(literal) => Display::fmt(literal, f),
//             Self::Scalar(literal) => Display::fmt(literal, f),
//             Self::String(literal) => Display::fmt(literal, f),
//         }
//     }
// }
