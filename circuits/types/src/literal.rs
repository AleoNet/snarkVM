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

#[derive(Clone, EnumIndex)]
pub enum Literal<E: Environment> {
    /// The Aleo address type.
    Address(Address<E>),
    /// The boolean type.
    Boolean(Boolean<E>),
    // /// A custom type.
    // Custom(Custom<E>),
    /// The field type (base field).
    Field(Field<E>),
    /// The group type (affine).
    Group(Group<E>),
    /// The 8-bit signed integer type.
    I8(I8<E>),
    /// The 16-bit signed integer type.
    I16(I16<E>),
    /// The 32-bit signed integer type.
    I32(I32<E>),
    /// The 64-bit signed integer type.
    I64(I64<E>),
    /// The 128-bit signed integer type.
    I128(I128<E>),
    /// The 8-bit unsigned integer type.
    U8(U8<E>),
    /// The 16-bit unsigned integer type.
    U16(U16<E>),
    /// The 32-bit unsigned integer type.
    U32(U32<E>),
    /// The 64-bit unsigned integer type.
    U64(U64<E>),
    /// The 128-bit unsigned integer type.
    U128(U128<E>),
    /// The scalar type (scalar field).
    Scalar(Scalar<E>),
    /// The string type.
    String(StringType<E>),
}

impl<E: Environment> Literal<E> {
    /// Returns the type name of the literal.
    pub fn type_name(&self) -> &'static str {
        match self {
            Self::Address(..) => Address::<E>::type_name(),
            Self::Boolean(..) => Boolean::<E>::type_name(),
            // Self::Custom(custom) => custom.type_name(),
            Self::Field(..) => Field::<E>::type_name(),
            Self::Group(..) => Group::<E>::type_name(),
            Self::I8(..) => I8::<E>::type_name(),
            Self::I16(..) => I16::<E>::type_name(),
            Self::I32(..) => I32::<E>::type_name(),
            Self::I64(..) => I64::<E>::type_name(),
            Self::I128(..) => I128::<E>::type_name(),
            Self::U8(..) => U8::<E>::type_name(),
            Self::U16(..) => U16::<E>::type_name(),
            Self::U32(..) => U32::<E>::type_name(),
            Self::U64(..) => U64::<E>::type_name(),
            Self::U128(..) => U128::<E>::type_name(),
            Self::Scalar(..) => Scalar::<E>::type_name(),
            Self::String(..) => StringType::<E>::type_name(),
        }
    }

    /// Returns the mode of the literal.
    pub fn mode(&self) -> Mode {
        match self {
            Self::Address(literal) => literal.eject_mode(),
            Self::Boolean(literal) => literal.eject_mode(),
            // Self::Custom(literal) => literal.eject_mode(),
            Self::Field(literal) => literal.eject_mode(),
            Self::Group(literal) => literal.eject_mode(),
            Self::I8(literal) => literal.eject_mode(),
            Self::I16(literal) => literal.eject_mode(),
            Self::I32(literal) => literal.eject_mode(),
            Self::I64(literal) => literal.eject_mode(),
            Self::I128(literal) => literal.eject_mode(),
            Self::U8(literal) => literal.eject_mode(),
            Self::U16(literal) => literal.eject_mode(),
            Self::U32(literal) => literal.eject_mode(),
            Self::U64(literal) => literal.eject_mode(),
            Self::U128(literal) => literal.eject_mode(),
            Self::Scalar(literal) => literal.eject_mode(),
            Self::String(literal) => literal.eject_mode(),
        }
    }

    /// Returns `true` if the literal is a constant.
    pub fn is_constant(&self) -> bool {
        self.mode().is_constant()
    }

    /// Returns `true` if the literal is public.
    pub fn is_public(&self) -> bool {
        self.mode().is_public()
    }

    /// Returns `true` if the literal is private.
    pub fn is_private(&self) -> bool {
        self.mode().is_private()
    }
}

#[allow(clippy::let_and_return)]
impl<E: Environment> Parser for Literal<E> {
    type Environment = E;

    /// Parses a string into a literal.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        alt((
            map(Address::parse, |literal| Self::Address(literal)),
            map(Boolean::parse, |literal| Self::Boolean(literal)),
            // map(Custom::parse, |literal| Self::Custom(literal)),
            map(Field::parse, |literal| Self::Field(literal)),
            map(Group::parse, |literal| Self::Group(literal)),
            map(I8::parse, |literal| Self::I8(literal)),
            map(I16::parse, |literal| Self::I16(literal)),
            map(I32::parse, |literal| Self::I32(literal)),
            map(I64::parse, |literal| Self::I64(literal)),
            map(I128::parse, |literal| Self::I128(literal)),
            map(U8::parse, |literal| Self::U8(literal)),
            map(U16::parse, |literal| Self::U16(literal)),
            map(U32::parse, |literal| Self::U32(literal)),
            map(U64::parse, |literal| Self::U64(literal)),
            map(U128::parse, |literal| Self::U128(literal)),
            map(Scalar::parse, |literal| Self::Scalar(literal)),
            map(StringType::parse, |literal| Self::String(literal)),
        ))(string)
    }
}

impl<E: Environment> Debug for Literal<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Address(literal) => Debug::fmt(literal, f),
            Self::Boolean(literal) => Debug::fmt(literal, f),
            // Self::Custom(literal) => Debug::fmt(literal, f),
            Self::Field(literal) => Debug::fmt(literal, f),
            Self::Group(literal) => Debug::fmt(literal, f),
            Self::I8(literal) => Debug::fmt(literal, f),
            Self::I16(literal) => Debug::fmt(literal, f),
            Self::I32(literal) => Debug::fmt(literal, f),
            Self::I64(literal) => Debug::fmt(literal, f),
            Self::I128(literal) => Debug::fmt(literal, f),
            Self::U8(literal) => Debug::fmt(literal, f),
            Self::U16(literal) => Debug::fmt(literal, f),
            Self::U32(literal) => Debug::fmt(literal, f),
            Self::U64(literal) => Debug::fmt(literal, f),
            Self::U128(literal) => Debug::fmt(literal, f),
            Self::Scalar(literal) => Debug::fmt(literal, f),
            Self::String(literal) => Debug::fmt(literal, f),
        }
    }
}

impl<E: Environment> Display for Literal<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Address(literal) => Display::fmt(literal, f),
            Self::Boolean(literal) => Display::fmt(literal, f),
            // Self::Custom(literal) => Display::fmt(literal, f),
            Self::Field(literal) => Display::fmt(literal, f),
            Self::Group(literal) => Display::fmt(literal, f),
            Self::I8(literal) => Display::fmt(literal, f),
            Self::I16(literal) => Display::fmt(literal, f),
            Self::I32(literal) => Display::fmt(literal, f),
            Self::I64(literal) => Display::fmt(literal, f),
            Self::I128(literal) => Display::fmt(literal, f),
            Self::U8(literal) => Display::fmt(literal, f),
            Self::U16(literal) => Display::fmt(literal, f),
            Self::U32(literal) => Display::fmt(literal, f),
            Self::U64(literal) => Display::fmt(literal, f),
            Self::U128(literal) => Display::fmt(literal, f),
            Self::Scalar(literal) => Display::fmt(literal, f),
            Self::String(literal) => Display::fmt(literal, f),
        }
    }
}

impl<E: Environment> PartialEq for Literal<E> {
    fn eq(&self, other: &Self) -> bool {
        self.mode() == other.mode()
            && match (self, other) {
                (Self::Address(this), Self::Address(that)) => this.eject_value() == that.eject_value(),
                (Self::Boolean(this), Self::Boolean(that)) => this.eject_value() == that.eject_value(),
                // (Self::Custom(this), Self::Custom(that)) => this.eject_value() == that.eject_value(),
                (Self::Field(this), Self::Field(that)) => this.eject_value() == that.eject_value(),
                (Self::Group(this), Self::Group(that)) => this.eject_value() == that.eject_value(),
                (Self::I8(this), Self::I8(that)) => this.eject_value() == that.eject_value(),
                (Self::I16(this), Self::I16(that)) => this.eject_value() == that.eject_value(),
                (Self::I32(this), Self::I32(that)) => this.eject_value() == that.eject_value(),
                (Self::I64(this), Self::I64(that)) => this.eject_value() == that.eject_value(),
                (Self::I128(this), Self::I128(that)) => this.eject_value() == that.eject_value(),
                (Self::U8(this), Self::U8(that)) => this.eject_value() == that.eject_value(),
                (Self::U16(this), Self::U16(that)) => this.eject_value() == that.eject_value(),
                (Self::U32(this), Self::U32(that)) => this.eject_value() == that.eject_value(),
                (Self::U64(this), Self::U64(that)) => this.eject_value() == that.eject_value(),
                (Self::U128(this), Self::U128(that)) => this.eject_value() == that.eject_value(),
                (Self::Scalar(this), Self::Scalar(that)) => this.eject_value() == that.eject_value(),
                _ => false,
            }
    }
}

impl<E: Environment> Eq for Literal<E> {}

impl<E: Environment> ToBits for Literal<E> {
    type Boolean = Boolean<E>;

    /// Returns the little-endian bits of the literal.
    fn to_bits_le(&self) -> Vec<Boolean<E>> {
        match self {
            Self::Address(literal) => literal.to_bits_le(),
            Self::Boolean(literal) => literal.to_bits_le(),
            // Self::Custom(literal) => literal.to_bits_le(),
            Self::Field(literal) => literal.to_bits_le(),
            Self::Group(literal) => literal.to_bits_le(),
            Self::I8(literal) => literal.to_bits_le(),
            Self::I16(literal) => literal.to_bits_le(),
            Self::I32(literal) => literal.to_bits_le(),
            Self::I64(literal) => literal.to_bits_le(),
            Self::I128(literal) => literal.to_bits_le(),
            Self::U8(literal) => literal.to_bits_le(),
            Self::U16(literal) => literal.to_bits_le(),
            Self::U32(literal) => literal.to_bits_le(),
            Self::U64(literal) => literal.to_bits_le(),
            Self::U128(literal) => literal.to_bits_le(),
            Self::Scalar(literal) => literal.to_bits_le(),
            Self::String(literal) => literal.to_bits_le(),
        }
    }

    /// Returns the big-endian bits of the literal.
    fn to_bits_be(&self) -> Vec<Boolean<E>> {
        match self {
            Self::Address(literal) => literal.to_bits_be(),
            Self::Boolean(literal) => literal.to_bits_be(),
            // Self::Custom(literal) => literal.to_bits_be(),
            Self::Field(literal) => literal.to_bits_be(),
            Self::Group(literal) => literal.to_bits_be(),
            Self::I8(literal) => literal.to_bits_be(),
            Self::I16(literal) => literal.to_bits_be(),
            Self::I32(literal) => literal.to_bits_be(),
            Self::I64(literal) => literal.to_bits_be(),
            Self::I128(literal) => literal.to_bits_be(),
            Self::U8(literal) => literal.to_bits_be(),
            Self::U16(literal) => literal.to_bits_be(),
            Self::U32(literal) => literal.to_bits_be(),
            Self::U64(literal) => literal.to_bits_be(),
            Self::U128(literal) => literal.to_bits_be(),
            Self::Scalar(literal) => literal.to_bits_be(),
            Self::String(literal) => literal.to_bits_be(),
        }
    }
}

impl<E: Environment> FromBytes for Literal<E> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let index = u16::read_le(&mut reader)?;
        let mode = Mode::read_le(&mut reader)?;
        let literal = match index {
            0 => Self::Address(Address::new(mode, FromBytes::read_le(&mut reader)?)),
            1 => Self::Boolean(Boolean::new(mode, FromBytes::read_le(&mut reader)?)),
            // 2 => Self::Custom(Custom::new(mode, FromBytes::read_le(&mut reader)?)),
            3 => Self::Field(Field::new(mode, FromBytes::read_le(&mut reader)?)),
            4 => Self::Group(Group::new(mode, FromBytes::read_le(&mut reader)?)),
            5 => Self::I8(I8::new(mode, FromBytes::read_le(&mut reader)?)),
            6 => Self::I16(I16::new(mode, FromBytes::read_le(&mut reader)?)),
            7 => Self::I32(I32::new(mode, FromBytes::read_le(&mut reader)?)),
            8 => Self::I64(I64::new(mode, FromBytes::read_le(&mut reader)?)),
            9 => Self::I128(I128::new(mode, FromBytes::read_le(&mut reader)?)),
            10 => Self::U8(U8::new(mode, FromBytes::read_le(&mut reader)?)),
            11 => Self::U16(U16::new(mode, FromBytes::read_le(&mut reader)?)),
            12 => Self::U32(U32::new(mode, FromBytes::read_le(&mut reader)?)),
            13 => Self::U64(U64::new(mode, FromBytes::read_le(&mut reader)?)),
            14 => Self::U128(U128::new(mode, FromBytes::read_le(&mut reader)?)),
            15 => Self::Scalar(Scalar::new(mode, FromBytes::read_le(&mut reader)?)),
            16 => {
                let size = u32::read_le(&mut reader)?;
                let mut buffer = vec![0u8; size as usize];
                reader.read_exact(&mut buffer)?;
                Self::String(StringType::new(mode, String::from_utf8(buffer).map_err(|e| error(format!("{e}")))?))
            }
            _ => return Err(error(format!("FromBytes failed to parse a literal of type {index}"))),
        };
        Ok(literal)
    }
}

impl<E: Environment> ToBytes for Literal<E> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (self.enum_index() as u16).write_le(&mut writer)?;
        self.mode().write_le(&mut writer)?;
        match self {
            Self::Address(literal) => literal.eject_value().write_le(&mut writer),
            Self::Boolean(literal) => literal.eject_value().write_le(&mut writer),
            // Self::Custom(literal) => literal.eject_value().write_le(&mut writer),
            Self::Field(literal) => literal.eject_value().write_le(&mut writer),
            Self::Group(literal) => literal.eject_value().write_le(&mut writer),
            Self::I8(literal) => literal.eject_value().write_le(&mut writer),
            Self::I16(literal) => literal.eject_value().write_le(&mut writer),
            Self::I32(literal) => literal.eject_value().write_le(&mut writer),
            Self::I64(literal) => literal.eject_value().write_le(&mut writer),
            Self::I128(literal) => literal.eject_value().write_le(&mut writer),
            Self::U8(literal) => literal.eject_value().write_le(&mut writer),
            Self::U16(literal) => literal.eject_value().write_le(&mut writer),
            Self::U32(literal) => literal.eject_value().write_le(&mut writer),
            Self::U64(literal) => literal.eject_value().write_le(&mut writer),
            Self::U128(literal) => literal.eject_value().write_le(&mut writer),
            Self::Scalar(literal) => literal.eject_value().write_le(&mut writer),
            Self::String(literal) => {
                let string = literal.eject_value();
                (string.as_bytes().len() as u32).write_le(&mut writer)?;
                string.as_bytes().write_le(&mut writer)
            }
        }
    }
}
