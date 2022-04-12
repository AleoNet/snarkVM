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

use crate::Program;
use snarkvm_circuits::prelude::*;
use snarkvm_utilities::{
    error,
    io::{Read, Result as IoResult, Write},
    FromBytes,
    ToBytes,
};

use enum_index::EnumIndex;

/// Trait to infer the output type of an instruction.
pub trait OutputType {
    type Input;
    // Note that `Output` is expected to be a `LiteralType` or a tuple of `LiteralType`s.
    type Output;

    fn output_type(input_type: &Self::Input) -> Self::Output;
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, EnumIndex)]
pub enum LiteralType<P> {
    /// The Aleo address type.
    Address(Mode),
    /// The boolean type.
    Boolean(Mode),
    /// The field type (base field).
    Field(Mode),
    /// The group type (affine).
    Group(Mode),
    /// The 8-bit signed integer type.
    I8(Mode),
    /// The 16-bit signed integer type.
    I16(Mode),
    /// The 32-bit signed integer type.
    I32(Mode),
    /// The 64-bit signed integer type.
    I64(Mode),
    /// The 128-bit signed integer type.
    I128(Mode),
    /// The 8-bit unsigned integer type.
    U8(Mode),
    /// The 16-bit unsigned integer type.
    U16(Mode),
    /// The 32-bit unsigned integer type.
    U32(Mode),
    /// The 64-bit unsigned integer type.
    U64(Mode),
    /// The 128-bit unsigned integer type.
    U128(Mode),
    /// The scalar type (scalar field).
    Scalar(Mode),
    /// The string type.
    String(Mode, Option<P>),
}

impl<P: Program> LiteralType<P> {
    /// Returns the literal type name.
    pub fn type_name(&self) -> &str {
        match self {
            Self::Address(..) => Address::<P::Environment>::type_name(),
            Self::Boolean(..) => Boolean::<P::Environment>::type_name(),
            Self::Field(..) => Field::<P::Environment>::type_name(),
            Self::Group(..) => Group::<P::Environment>::type_name(),
            Self::I8(..) => I8::<P::Environment>::type_name(),
            Self::I16(..) => I16::<P::Environment>::type_name(),
            Self::I32(..) => I32::<P::Environment>::type_name(),
            Self::I64(..) => I64::<P::Environment>::type_name(),
            Self::I128(..) => I128::<P::Environment>::type_name(),
            Self::U8(..) => U8::<P::Environment>::type_name(),
            Self::U16(..) => U16::<P::Environment>::type_name(),
            Self::U32(..) => U32::<P::Environment>::type_name(),
            Self::U64(..) => U64::<P::Environment>::type_name(),
            Self::U128(..) => U128::<P::Environment>::type_name(),
            Self::Scalar(..) => Scalar::<P::Environment>::type_name(),
            Self::String(..) => StringType::<P::Environment>::type_name(),
        }
    }

    /// Returns the mode.
    pub fn mode(&self) -> &Mode {
        match self {
            Self::Address(mode) => mode,
            Self::Boolean(mode) => mode,
            Self::Field(mode) => mode,
            Self::Group(mode) => mode,
            Self::I8(mode) => mode,
            Self::I16(mode) => mode,
            Self::I32(mode) => mode,
            Self::I64(mode) => mode,
            Self::I128(mode) => mode,
            Self::U8(mode) => mode,
            Self::U16(mode) => mode,
            Self::U32(mode) => mode,
            Self::U64(mode) => mode,
            Self::U128(mode) => mode,
            Self::Scalar(mode) => mode,
            Self::String(mode, ..) => mode,
        }
    }

    /// Returns `true` if the literal type is a constant.
    pub fn is_constant(&self) -> bool {
        self.mode().is_constant()
    }

    /// Returns `true` if the literal type is public.
    pub fn is_public(&self) -> bool {
        self.mode().is_public()
    }

    /// Returns `true` if the literal type is private.
    pub fn is_private(&self) -> bool {
        self.mode().is_private()
    }
}

impl<P: Program> From<Literal<P::Environment>> for LiteralType<P> {
    #[inline]
    fn from(literal: Literal<P::Environment>) -> Self {
        Self::from(&literal)
    }
}

impl<P: Program> From<&Literal<P::Environment>> for LiteralType<P> {
    #[inline]
    fn from(literal: &Literal<P::Environment>) -> Self {
        let mode = literal.eject_mode();
        match literal {
            Literal::Address(..) => Self::Address(mode),
            Literal::Boolean(..) => Self::Boolean(mode),
            Literal::Field(..) => Self::Field(mode),
            Literal::Group(..) => Self::Group(mode),
            Literal::I8(..) => Self::I8(mode),
            Literal::I16(..) => Self::I16(mode),
            Literal::I32(..) => Self::I32(mode),
            Literal::I64(..) => Self::I64(mode),
            Literal::I128(..) => Self::I128(mode),
            Literal::U8(..) => Self::U8(mode),
            Literal::U16(..) => Self::U16(mode),
            Literal::U32(..) => Self::U32(mode),
            Literal::U64(..) => Self::U64(mode),
            Literal::U128(..) => Self::U128(mode),
            Literal::Scalar(..) => Self::Scalar(mode),
            Literal::String(..) => Self::String(mode, None),
        }
    }
}

#[allow(clippy::let_and_return)]
impl<P: Program> Parser for LiteralType<P> {
    type Environment = P::Environment;

    /// Parses a string into a literal type.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the type from the string.
        let result = alt((
            map(pair(pair(tag(Address::<P::Environment>::type_name()), tag(".")), Mode::parse), |(_, mode)| {
                Self::Address(mode)
            }),
            map(pair(pair(tag(Boolean::<P::Environment>::type_name()), tag(".")), Mode::parse), |(_, mode)| {
                Self::Boolean(mode)
            }),
            map(pair(pair(tag(Field::<P::Environment>::type_name()), tag(".")), Mode::parse), |(_, mode)| {
                Self::Field(mode)
            }),
            map(pair(pair(tag(Group::<P::Environment>::type_name()), tag(".")), Mode::parse), |(_, mode)| {
                Self::Group(mode)
            }),
            map(pair(pair(tag(I8::<P::Environment>::type_name()), tag(".")), Mode::parse), |(_, mode)| Self::I8(mode)),
            map(pair(pair(tag(I16::<P::Environment>::type_name()), tag(".")), Mode::parse), |(_, mode)| {
                Self::I16(mode)
            }),
            map(pair(pair(tag(I32::<P::Environment>::type_name()), tag(".")), Mode::parse), |(_, mode)| {
                Self::I32(mode)
            }),
            map(pair(pair(tag(I64::<P::Environment>::type_name()), tag(".")), Mode::parse), |(_, mode)| {
                Self::I64(mode)
            }),
            map(pair(pair(tag(I128::<P::Environment>::type_name()), tag(".")), Mode::parse), |(_, mode)| {
                Self::I128(mode)
            }),
            map(pair(pair(tag(U8::<P::Environment>::type_name()), tag(".")), Mode::parse), |(_, mode)| Self::U8(mode)),
            map(pair(pair(tag(U16::<P::Environment>::type_name()), tag(".")), Mode::parse), |(_, mode)| {
                Self::U16(mode)
            }),
            map(pair(pair(tag(U32::<P::Environment>::type_name()), tag(".")), Mode::parse), |(_, mode)| {
                Self::U32(mode)
            }),
            map(pair(pair(tag(U64::<P::Environment>::type_name()), tag(".")), Mode::parse), |(_, mode)| {
                Self::U64(mode)
            }),
            map(pair(pair(tag(U128::<P::Environment>::type_name()), tag(".")), Mode::parse), |(_, mode)| {
                Self::U128(mode)
            }),
            map(pair(pair(tag(Scalar::<P::Environment>::type_name()), tag(".")), Mode::parse), |(_, mode)| {
                Self::Scalar(mode)
            }),
            map(pair(pair(tag(StringType::<P::Environment>::type_name()), tag(".")), Mode::parse), |(_, mode)| {
                Self::String(mode, None)
            }),
        ))(string);
        result
    }
}

impl<P: Program> Debug for LiteralType<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}.{}", self.type_name(), self.mode())
    }
}

impl<P: Program> Display for LiteralType<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}.{}", self.type_name(), self.mode())
    }
}

impl<P: Program> FromBytes for LiteralType<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let index = u16::read_le(&mut reader)?;
        let mode = Mode::read_le(&mut reader)?;
        let literal = match index {
            0 => Self::Address(mode),
            1 => Self::Boolean(mode),
            2 => Self::Field(mode),
            3 => Self::Group(mode),
            4 => Self::I8(mode),
            5 => Self::I16(mode),
            6 => Self::I32(mode),
            7 => Self::I64(mode),
            8 => Self::I128(mode),
            9 => Self::U8(mode),
            10 => Self::U16(mode),
            11 => Self::U32(mode),
            12 => Self::U64(mode),
            13 => Self::U128(mode),
            14 => Self::Scalar(mode),
            15 => Self::String(mode, None),
            16.. => return Err(error(format!("Failed to deserialize literal type variant {index}"))),
        };
        Ok(literal)
    }
}

impl<P: Program> ToBytes for LiteralType<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (self.enum_index() as u16).write_le(&mut writer)?;
        self.mode().write_le(&mut writer)
    }
}
