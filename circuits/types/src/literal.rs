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
    io::{Read, Result as IoResult, Write},
    FromBytes,
    ToBytes,
};

/// The literal enum represents all supported circuit types in snarkVM.
#[derive(Clone, EnumIndex)]
pub enum Literal<E: Environment> {
    /// The Aleo address type.
    Address(Address<E>),
    /// The boolean type.
    Boolean(Boolean<E>),
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
    pub fn type_name(&self) -> &str {
        match self {
            Self::Address(..) => Address::<E>::type_name(),
            Self::Boolean(..) => Boolean::<E>::type_name(),
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
}

impl<E: Environment> Inject for Literal<E> {
    type Primitive = Primitive<E>;

    /// Initializes a new literal from a primitive.
    fn new(mode: Mode, value: Self::Primitive) -> Self {
        match value {
            Primitive::Address(address) => Self::Address(Address::new(mode, address)),
            Primitive::Boolean(boolean) => Self::Boolean(Boolean::new(mode, boolean)),
            Primitive::Field(field) => Self::Field(Field::new(mode, field)),
            Primitive::Group(group) => Self::Group(Group::new(mode, group)),
            Primitive::I8(i8) => Self::I8(I8::new(mode, i8)),
            Primitive::I16(i16) => Self::I16(I16::new(mode, i16)),
            Primitive::I32(i32) => Self::I32(I32::new(mode, i32)),
            Primitive::I64(i64) => Self::I64(I64::new(mode, i64)),
            Primitive::I128(i128) => Self::I128(I128::new(mode, i128)),
            Primitive::U8(u8) => Self::U8(U8::new(mode, u8)),
            Primitive::U16(u16) => Self::U16(U16::new(mode, u16)),
            Primitive::U32(u32) => Self::U32(U32::new(mode, u32)),
            Primitive::U64(u64) => Self::U64(U64::new(mode, u64)),
            Primitive::U128(u128) => Self::U128(U128::new(mode, u128)),
            Primitive::Scalar(scalar) => Self::Scalar(Scalar::new(mode, scalar)),
            Primitive::String(string) => Self::String(StringType::new(mode, string)),
        }
    }
}

impl<E: Environment> Eject for Literal<E> {
    type Primitive = Primitive<E>;

    ///
    /// Ejects the mode of the object.
    ///
    fn eject_mode(&self) -> Mode {
        match self {
            Self::Address(literal) => literal.eject_mode(),
            Self::Boolean(literal) => literal.eject_mode(),
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

    ///
    /// Ejects the object into its primitives.
    ///
    fn eject_value(&self) -> Self::Primitive {
        match self {
            Self::Address(literal) => Primitive::Address(literal.eject_value()),
            Self::Boolean(literal) => Primitive::Boolean(literal.eject_value()),
            Self::Field(literal) => Primitive::Field(literal.eject_value()),
            Self::Group(literal) => Primitive::Group(literal.eject_value()),
            Self::I8(literal) => Primitive::I8(literal.eject_value()),
            Self::I16(literal) => Primitive::I16(literal.eject_value()),
            Self::I32(literal) => Primitive::I32(literal.eject_value()),
            Self::I64(literal) => Primitive::I64(literal.eject_value()),
            Self::I128(literal) => Primitive::I128(literal.eject_value()),
            Self::U8(literal) => Primitive::U8(literal.eject_value()),
            Self::U16(literal) => Primitive::U16(literal.eject_value()),
            Self::U32(literal) => Primitive::U32(literal.eject_value()),
            Self::U64(literal) => Primitive::U64(literal.eject_value()),
            Self::U128(literal) => Primitive::U128(literal.eject_value()),
            Self::Scalar(literal) => Primitive::Scalar(literal.eject_value()),
            Self::String(literal) => Primitive::String(literal.eject_value()),
        }
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

impl<E: Environment> ToBits for Literal<E> {
    type Boolean = Boolean<E>;

    /// Returns the little-endian bits of the literal.
    fn to_bits_le(&self) -> Vec<Boolean<E>> {
        (&self).to_bits_le()
    }

    /// Returns the big-endian bits of the literal.
    fn to_bits_be(&self) -> Vec<Boolean<E>> {
        (&self).to_bits_be()
    }
}

impl<E: Environment> ToBits for &Literal<E> {
    type Boolean = Boolean<E>;

    /// Returns the little-endian bits of the literal.
    fn to_bits_le(&self) -> Vec<Boolean<E>> {
        match self {
            Literal::Address(literal) => literal.to_bits_le(),
            Literal::Boolean(literal) => literal.to_bits_le(),
            Literal::Field(literal) => literal.to_bits_le(),
            Literal::Group(literal) => literal.to_bits_le(),
            Literal::I8(literal) => literal.to_bits_le(),
            Literal::I16(literal) => literal.to_bits_le(),
            Literal::I32(literal) => literal.to_bits_le(),
            Literal::I64(literal) => literal.to_bits_le(),
            Literal::I128(literal) => literal.to_bits_le(),
            Literal::U8(literal) => literal.to_bits_le(),
            Literal::U16(literal) => literal.to_bits_le(),
            Literal::U32(literal) => literal.to_bits_le(),
            Literal::U64(literal) => literal.to_bits_le(),
            Literal::U128(literal) => literal.to_bits_le(),
            Literal::Scalar(literal) => literal.to_bits_le(),
            Literal::String(literal) => literal.to_bits_le(),
        }
    }

    /// Returns the big-endian bits of the literal.
    fn to_bits_be(&self) -> Vec<Boolean<E>> {
        match self {
            Literal::Address(literal) => literal.to_bits_be(),
            Literal::Boolean(literal) => literal.to_bits_be(),
            Literal::Field(literal) => literal.to_bits_be(),
            Literal::Group(literal) => literal.to_bits_be(),
            Literal::I8(literal) => literal.to_bits_be(),
            Literal::I16(literal) => literal.to_bits_be(),
            Literal::I32(literal) => literal.to_bits_be(),
            Literal::I64(literal) => literal.to_bits_be(),
            Literal::I128(literal) => literal.to_bits_be(),
            Literal::U8(literal) => literal.to_bits_be(),
            Literal::U16(literal) => literal.to_bits_be(),
            Literal::U32(literal) => literal.to_bits_be(),
            Literal::U64(literal) => literal.to_bits_be(),
            Literal::U128(literal) => literal.to_bits_be(),
            Literal::Scalar(literal) => literal.to_bits_be(),
            Literal::String(literal) => literal.to_bits_be(),
        }
    }
}

impl<E: Environment> FromBytes for Literal<E> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let mode = Mode::read_le(&mut reader)?;
        let primitive = Primitive::read_le(&mut reader)?;
        Ok(Self::new(mode, primitive))
    }
}

impl<E: Environment> ToBytes for Literal<E> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.eject_mode().write_le(&mut writer)?;
        self.eject_value().write_le(&mut writer)
    }
}
