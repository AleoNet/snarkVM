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

use snarkvm_utilities::{
    error,
    io::{Read, Result as IoResult, Write},
    FromBytes,
    ToBytes,
};

use core::fmt::{self, Debug, Display};
use enum_index::EnumIndex;use enum_index::IndexEnum;

#[derive(Copy, Clone, PartialEq, Eq, Hash, EnumIndex, IndexEnum)]
pub enum LiteralType {
    /// The Aleo address type.
    Address,
    /// The boolean type.
    Boolean,
    /// The field type (base field).
    Field,
    /// The group type (affine).
    Group,
    /// The 8-bit signed integer type.
    I8,
    /// The 16-bit signed integer type.
    I16,
    /// The 32-bit signed integer type.
    I32,
    /// The 64-bit signed integer type.
    I64,
    /// The 128-bit signed integer type.
    I128,
    /// The 8-bit unsigned integer type.
    U8,
    /// The 16-bit unsigned integer type.
    U16,
    /// The 32-bit unsigned integer type.
    U32,
    /// The 64-bit unsigned integer type.
    U64,
    /// The 128-bit unsigned integer type.
    U128,
    /// The scalar type (scalar field).
    Scalar,
    /// The string type.
    String,
}

// impl LiteralType {
//     /// Returns the literal type name.
//     pub fn type_name<A: Aleo>(&self) -> &str {
//         match self {
//             Self::Address(..) => Address::<A>::type_name(),
//             Self::Boolean(..) => Boolean::<A>::type_name(),
//             Self::Field(..) => Field::<A>::type_name(),
//             Self::Group(..) => Group::<A>::type_name(),
//             Self::I8(..) => I8::<A>::type_name(),
//             Self::I16(..) => I16::<A>::type_name(),
//             Self::I32(..) => I32::<A>::type_name(),
//             Self::I64(..) => I64::<A>::type_name(),
//             Self::I128(..) => I128::<A>::type_name(),
//             Self::U8(..) => U8::<A>::type_name(),
//             Self::U16(..) => U16::<A>::type_name(),
//             Self::U32(..) => U32::<A>::type_name(),
//             Self::U64(..) => U64::<A>::type_name(),
//             Self::U128(..) => U128::<A>::type_name(),
//             Self::Scalar(..) => Scalar::<A>::type_name(),
//             Self::String(..) => StringType::<A>::type_name(),
//         }
//     }
// }
//
// #[allow(clippy::let_and_return)]
// impl Parser for LiteralType {
//     type Environment = A;
//
//     /// Parses a string into a literal type.
//     #[inline]
//     fn parse(string: &str) -> ParserResult<Self> {
//         // Parse the type from the string.
//         let result = alt((
//             map(tag(Address::<A>::type_name()), |_| Self::Address),
//             map(tag(Boolean::<A>::type_name()), |_| Self::Boolean),
//             map(tag(Field::<A>::type_name()), |_| Self::Field),
//             map(tag(Group::<A>::type_name()), |_| Self::Group),
//             map(tag(I8::<A>::type_name()), |_| Self::I8),
//             map(tag(I16::<A>::type_name()), |_| Self::I16),
//             map(tag(I32::<A>::type_name()), |_| Self::I32),
//             map(tag(I64::<A>::type_name()), |_| Self::I64),
//             map(tag(I128::<A>::type_name()), |_| Self::I128),
//             map(tag(U8::<A>::type_name()), |_| Self::U8),
//             map(tag(U16::<A>::type_name()), |_| Self::U16),
//             map(tag(U32::<A>::type_name()), |_| Self::U32),
//             map(tag(U64::<A>::type_name()), |_| Self::U64),
//             map(tag(U128::<A>::type_name()), |_| Self::U128),
//             map(tag(Scalar::<A>::type_name()), |_| Self::Scalar),
//             map(tag(StringType::<A>::type_name()), |_| Self::String),
//         ))(string);
//         result
//     }
// }
//
// impl Debug for LiteralType {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         write!(f, "{}", self.type_name())
//     }
// }
//
// impl Display for LiteralType {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         write!(f, "{}", self.type_name())
//     }
// }

impl FromBytes for LiteralType {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let index = u16::read_le(&mut reader)?;
        Self::index_enum(index as usize).ok_or(error(format!("Failed to deserialize literal type variant {index}")))
    }
}

impl ToBytes for LiteralType {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (self.enum_index() as u16).write_le(&mut writer)
    }
}
