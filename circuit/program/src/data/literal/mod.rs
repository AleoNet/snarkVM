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
mod to_fields;
mod to_type;
mod variant;

use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::prelude::*;

/// The literal enum represents all supported circuit types in snarkVM.
#[derive(Clone)]
pub enum Literal<A: Aleo> {
    /// The Aleo address type.
    Address(Address<A>),
    /// The boolean type.
    Boolean(Boolean<A>),
    /// The field type (base field).
    Field(Field<A>),
    /// The group type (affine).
    Group(Group<A>),
    /// The 8-bit signed integer type.
    I8(I8<A>),
    /// The 16-bit signed integer type.
    I16(I16<A>),
    /// The 32-bit signed integer type.
    I32(I32<A>),
    /// The 64-bit signed integer type.
    I64(I64<A>),
    /// The 128-bit signed integer type.
    I128(I128<A>),
    /// The 8-bit unsigned integer type.
    U8(U8<A>),
    /// The 16-bit unsigned integer type.
    U16(U16<A>),
    /// The 32-bit unsigned integer type.
    U32(U32<A>),
    /// The 64-bit unsigned integer type.
    U64(U64<A>),
    /// The 128-bit unsigned integer type.
    U128(U128<A>),
    /// The scalar type (scalar field).
    Scalar(Scalar<A>),
    /// The string type.
    String(StringType<A>),
}

#[cfg(console)]
impl<A: Aleo> Inject for Literal<A> {
    type Primitive = console::Literal<A::Network>;

    /// Initializes a new literal from a primitive.
    fn new(mode: Mode, value: Self::Primitive) -> Self {
        match value {
            Self::Primitive::Address(address) => Self::Address(Address::new(mode, address)),
            Self::Primitive::Boolean(boolean) => Self::Boolean(Boolean::new(mode, *boolean)),
            Self::Primitive::Field(field) => Self::Field(Field::new(mode, field)),
            Self::Primitive::Group(group) => Self::Group(Group::new(mode, group)),
            Self::Primitive::I8(i8) => Self::I8(I8::new(mode, i8)),
            Self::Primitive::I16(i16) => Self::I16(I16::new(mode, i16)),
            Self::Primitive::I32(i32) => Self::I32(I32::new(mode, i32)),
            Self::Primitive::I64(i64) => Self::I64(I64::new(mode, i64)),
            Self::Primitive::I128(i128) => Self::I128(I128::new(mode, i128)),
            Self::Primitive::U8(u8) => Self::U8(U8::new(mode, u8)),
            Self::Primitive::U16(u16) => Self::U16(U16::new(mode, u16)),
            Self::Primitive::U32(u32) => Self::U32(U32::new(mode, u32)),
            Self::Primitive::U64(u64) => Self::U64(U64::new(mode, u64)),
            Self::Primitive::U128(u128) => Self::U128(U128::new(mode, u128)),
            Self::Primitive::Scalar(scalar) => Self::Scalar(Scalar::new(mode, scalar)),
            Self::Primitive::String(string) => Self::String(StringType::new(mode, string)),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for Literal<A> {
    type Primitive = console::Literal<A::Network>;

    /// Ejects the mode of the literal.
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

    /// Ejects the literal into its primitive.
    fn eject_value(&self) -> Self::Primitive {
        match self {
            Self::Address(literal) => Self::Primitive::Address(literal.eject_value()),
            Self::Boolean(literal) => Self::Primitive::Boolean(console::Boolean::new(literal.eject_value())),
            Self::Field(literal) => Self::Primitive::Field(literal.eject_value()),
            Self::Group(literal) => Self::Primitive::Group(literal.eject_value()),
            Self::I8(literal) => Self::Primitive::I8(literal.eject_value()),
            Self::I16(literal) => Self::Primitive::I16(literal.eject_value()),
            Self::I32(literal) => Self::Primitive::I32(literal.eject_value()),
            Self::I64(literal) => Self::Primitive::I64(literal.eject_value()),
            Self::I128(literal) => Self::Primitive::I128(literal.eject_value()),
            Self::U8(literal) => Self::Primitive::U8(literal.eject_value()),
            Self::U16(literal) => Self::Primitive::U16(literal.eject_value()),
            Self::U32(literal) => Self::Primitive::U32(literal.eject_value()),
            Self::U64(literal) => Self::Primitive::U64(literal.eject_value()),
            Self::U128(literal) => Self::Primitive::U128(literal.eject_value()),
            Self::Scalar(literal) => Self::Primitive::Scalar(literal.eject_value()),
            Self::String(literal) => Self::Primitive::String(literal.eject_value()),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Parser for Literal<A> {
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

#[cfg(console)]
impl<A: Aleo> FromStr for Literal<A> {
    type Err = Error;

    /// Parses a string into a literal circuit.
    #[inline]
    fn from_str(string: &str) -> Result<Self> {
        match Self::parse(string) {
            Ok((remainder, object)) => {
                // Ensure the remainder is empty.
                ensure!(remainder.is_empty(), "Failed to parse string. Found invalid character in: \"{remainder}\"");
                // Return the object.
                Ok(object)
            }
            Err(error) => bail!("Failed to parse string. {error}"),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Literal<A> {
    /// Returns the type name of the literal.
    pub fn type_name(&self) -> &str {
        match self {
            Self::Address(..) => Address::<A>::type_name(),
            Self::Boolean(..) => Boolean::<A>::type_name(),
            Self::Field(..) => Field::<A>::type_name(),
            Self::Group(..) => Group::<A>::type_name(),
            Self::I8(..) => I8::<A>::type_name(),
            Self::I16(..) => I16::<A>::type_name(),
            Self::I32(..) => I32::<A>::type_name(),
            Self::I64(..) => I64::<A>::type_name(),
            Self::I128(..) => I128::<A>::type_name(),
            Self::U8(..) => U8::<A>::type_name(),
            Self::U16(..) => U16::<A>::type_name(),
            Self::U32(..) => U32::<A>::type_name(),
            Self::U64(..) => U64::<A>::type_name(),
            Self::U128(..) => U128::<A>::type_name(),
            Self::Scalar(..) => Scalar::<A>::type_name(),
            Self::String(..) => StringType::<A>::type_name(),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Debug for Literal<A> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

#[cfg(console)]
impl<A: Aleo> Display for Literal<A> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
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
