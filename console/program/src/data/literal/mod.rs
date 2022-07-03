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
mod parse;
mod size_in_bits;
mod to_bits;
mod to_type;
mod variant;

use crate::LiteralType;
use snarkvm_console_network::Network;
use snarkvm_console_types::{prelude::*, Boolean};

use enum_index::EnumIndex;

/// The literal enum represents all supported types in snarkVM.
#[derive(Clone, PartialEq, Eq, Hash, EnumIndex)]
pub enum Literal<N: Network> {
    /// The Aleo address type.
    Address(Address<N>),
    /// The boolean type.
    Boolean(Boolean<N>),
    /// The field type.
    Field(Field<N>),
    /// The group type.
    Group(Group<N>),
    /// The 8-bit signed integer type.
    I8(I8<N>),
    /// The 16-bit signed integer type.
    I16(I16<N>),
    /// The 32-bit signed integer type.
    I32(I32<N>),
    /// The 64-bit signed integer type.
    I64(I64<N>),
    /// The 128-bit signed integer type.
    I128(I128<N>),
    /// The 8-bit unsigned integer type.
    U8(U8<N>),
    /// The 16-bit unsigned integer type.
    U16(U16<N>),
    /// The 32-bit unsigned integer type.
    U32(U32<N>),
    /// The 64-bit unsigned integer type.
    U64(U64<N>),
    /// The 128-bit unsigned integer type.
    U128(U128<N>),
    /// The scalar type.
    Scalar(Scalar<N>),
    /// The string type.
    String(StringType<N>),
}

impl<N: Network> Literal<N> {
    /// Returns a randomly-sampled literal of the given literal type.
    pub fn sample<R: Rng + CryptoRng>(literal_type: LiteralType, rng: &mut R) -> Self {
        match literal_type {
            LiteralType::Address => Literal::Address(Address::new(Group::rand(rng))),
            LiteralType::Boolean => Literal::Boolean(Boolean::rand(rng)),
            LiteralType::Field => Literal::Field(Field::rand(rng)),
            LiteralType::Group => Literal::Group(Group::rand(rng)),
            LiteralType::I8 => Literal::I8(I8::rand(rng)),
            LiteralType::I16 => Literal::I16(I16::rand(rng)),
            LiteralType::I32 => Literal::I32(I32::rand(rng)),
            LiteralType::I64 => Literal::I64(I64::rand(rng)),
            LiteralType::I128 => Literal::I128(I128::rand(rng)),
            LiteralType::U8 => Literal::U8(U8::rand(rng)),
            LiteralType::U16 => Literal::U16(U16::rand(rng)),
            LiteralType::U32 => Literal::U32(U32::rand(rng)),
            LiteralType::U64 => Literal::U64(U64::rand(rng)),
            LiteralType::U128 => Literal::U128(U128::rand(rng)),
            LiteralType::Scalar => Literal::Scalar(Scalar::rand(rng)),
            LiteralType::String => Literal::String(StringType::new(
                &rng.sample_iter(&Alphanumeric)
                    .take((N::MAX_STRING_BYTES / 4) as usize)
                    .map(char::from)
                    .collect::<String>(),
            )),
        }
    }
}

impl<N: Network> FromBytes for Literal<N> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let index = u16::read_le(&mut reader)?;
        let literal = match index {
            0 => Self::Address(Address::new(
                Group::from_x_coordinate(Field::new(FromBytes::read_le(&mut reader)?))
                    .map_err(|e| error(format!("{e}")))?,
            )),
            1 => Self::Boolean(Boolean::new(FromBytes::read_le(&mut reader)?)),
            2 => Self::Field(Field::new(FromBytes::read_le(&mut reader)?)),
            3 => Self::Group(Group::new(FromBytes::read_le(&mut reader)?)),
            4 => Self::I8(I8::new(FromBytes::read_le(&mut reader)?)),
            5 => Self::I16(I16::new(FromBytes::read_le(&mut reader)?)),
            6 => Self::I32(I32::new(FromBytes::read_le(&mut reader)?)),
            7 => Self::I64(I64::new(FromBytes::read_le(&mut reader)?)),
            8 => Self::I128(I128::new(FromBytes::read_le(&mut reader)?)),
            9 => Self::U8(U8::new(FromBytes::read_le(&mut reader)?)),
            10 => Self::U16(U16::new(FromBytes::read_le(&mut reader)?)),
            11 => Self::U32(U32::new(FromBytes::read_le(&mut reader)?)),
            12 => Self::U64(U64::new(FromBytes::read_le(&mut reader)?)),
            13 => Self::U128(U128::new(FromBytes::read_le(&mut reader)?)),
            14 => Self::Scalar(Scalar::new(FromBytes::read_le(&mut reader)?)),
            15 => {
                let size = u32::read_le(&mut reader)?;
                if size > N::MAX_STRING_BYTES {
                    return Err(error(format!(
                        "String literal exceeds maximum length of {} bytes.",
                        N::MAX_STRING_BYTES
                    )));
                }
                let mut buffer = vec![0u8; size as usize];
                reader.read_exact(&mut buffer)?;

                let string = String::from_utf8(buffer).map_err(|e| error(format!("{e}")))?;
                Self::String(StringType::new(&string))
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
            Self::Address(primitive) => (*primitive).write_le(&mut writer),
            Self::Boolean(primitive) => (*primitive).write_le(&mut writer),
            Self::Field(primitive) => (*primitive).write_le(&mut writer),
            Self::Group(primitive) => (*primitive).write_le(&mut writer),
            Self::I8(primitive) => (*primitive).write_le(&mut writer),
            Self::I16(primitive) => (*primitive).write_le(&mut writer),
            Self::I32(primitive) => (*primitive).write_le(&mut writer),
            Self::I64(primitive) => (*primitive).write_le(&mut writer),
            Self::I128(primitive) => (*primitive).write_le(&mut writer),
            Self::U8(primitive) => (*primitive).write_le(&mut writer),
            Self::U16(primitive) => (*primitive).write_le(&mut writer),
            Self::U32(primitive) => (*primitive).write_le(&mut writer),
            Self::U64(primitive) => (*primitive).write_le(&mut writer),
            Self::U128(primitive) => (*primitive).write_le(&mut writer),
            Self::Scalar(primitive) => (*primitive).write_le(&mut writer),
            Self::String(primitive) => {
                ((*primitive).len() as u32).write_le(&mut writer)?;
                (*primitive).as_bytes().write_le(&mut writer)
            }
        }
    }
}
