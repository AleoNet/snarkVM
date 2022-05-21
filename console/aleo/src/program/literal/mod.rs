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

// mod from_bits;
// mod to_bits;

use crate::{Network, Address};

/// The literal enum represents all supported types in snarkVM.
#[derive(Clone, EnumIndex)]
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

// impl<N: Network> Inject for Literal<N> {
//     type Primitive = Primitive<N>;
//
//     /// Initializes a new literal from a primitive.
//     fn new(mode: Mode, value: Self::Primitive) -> Self {
//         match value {
//             Primitive::Address(address) => Self::Address(Address::new(mode, address)),
//             Primitive::Boolean(boolean) => Self::Boolean(Boolean::new(mode, boolean)),
//             Primitive::Field(field) => Self::Field(Field::new(mode, field)),
//             Primitive::Group(group) => Self::Group(Group::new(mode, group)),
//             Primitive::I8(i8) => Self::I8(I8::new(mode, i8)),
//             Primitive::I16(i16) => Self::I16(I16::new(mode, i16)),
//             Primitive::I32(i32) => Self::I32(I32::new(mode, i32)),
//             Primitive::I64(i64) => Self::I64(I64::new(mode, i64)),
//             Primitive::I128(i128) => Self::I128(I128::new(mode, i128)),
//             Primitive::U8(u8) => Self::U8(U8::new(mode, u8)),
//             Primitive::U16(u16) => Self::U16(U16::new(mode, u16)),
//             Primitive::U32(u32) => Self::U32(U32::new(mode, u32)),
//             Primitive::U64(u64) => Self::U64(U64::new(mode, u64)),
//             Primitive::U128(u128) => Self::U128(U128::new(mode, u128)),
//             Primitive::Scalar(scalar) => Self::Scalar(Scalar::new(mode, scalar)),
//             Primitive::String(string) => Self::String(StringType::new(mode, string)),
//         }
//     }
// }
//
// impl<N: Network> Eject for Literal<N> {
//     type Primitive = Primitive<N>;
//
//     ///
//     /// Ejects the mode of the object.
//     ///
//     fn eject_mode(&self) -> Mode {
//         match self {
//             Self::Address(literal) => literal.eject_mode(),
//             Self::Boolean(literal) => literal.eject_mode(),
//             Self::Field(literal) => literal.eject_mode(),
//             Self::Group(literal) => literal.eject_mode(),
//             Self::I8(literal) => literal.eject_mode(),
//             Self::I16(literal) => literal.eject_mode(),
//             Self::I32(literal) => literal.eject_mode(),
//             Self::I64(literal) => literal.eject_mode(),
//             Self::I128(literal) => literal.eject_mode(),
//             Self::U8(literal) => literal.eject_mode(),
//             Self::U16(literal) => literal.eject_mode(),
//             Self::U32(literal) => literal.eject_mode(),
//             Self::U64(literal) => literal.eject_mode(),
//             Self::U128(literal) => literal.eject_mode(),
//             Self::Scalar(literal) => literal.eject_mode(),
//             Self::String(literal) => literal.eject_mode(),
//         }
//     }
//
//     ///
//     /// Ejects the object into its primitives.
//     ///
//     fn eject_value(&self) -> Self::Primitive {
//         match self {
//             Self::Address(literal) => Primitive::Address(literal.eject_value()),
//             Self::Boolean(literal) => Primitive::Boolean(literal.eject_value()),
//             Self::Field(literal) => Primitive::Field(literal.eject_value()),
//             Self::Group(literal) => Primitive::Group(literal.eject_value()),
//             Self::I8(literal) => Primitive::I8(literal.eject_value()),
//             Self::I16(literal) => Primitive::I16(literal.eject_value()),
//             Self::I32(literal) => Primitive::I32(literal.eject_value()),
//             Self::I64(literal) => Primitive::I64(literal.eject_value()),
//             Self::I128(literal) => Primitive::I128(literal.eject_value()),
//             Self::U8(literal) => Primitive::U8(literal.eject_value()),
//             Self::U16(literal) => Primitive::U16(literal.eject_value()),
//             Self::U32(literal) => Primitive::U32(literal.eject_value()),
//             Self::U64(literal) => Primitive::U64(literal.eject_value()),
//             Self::U128(literal) => Primitive::U128(literal.eject_value()),
//             Self::Scalar(literal) => Primitive::Scalar(literal.eject_value()),
//             Self::String(literal) => Primitive::String(literal.eject_value()),
//         }
//     }
// }
//
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
