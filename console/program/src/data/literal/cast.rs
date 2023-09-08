// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

impl<N: Network> Literal<N> {
    /// Casts the literal to the given literal type.
    ///
    /// This method checks that the cast does not lose any bits of information,
    /// and returns an error if it does.
    ///
    /// The hierarchy of casting is as follows:
    ///  - (`Address`, `Group`) <-> `Field` <-> `Scalar` <-> `Integer` <-> `Boolean`
    ///  - `String` (not supported)
    /// Note that casting to left along the hierarchy always preserves information.
    pub fn cast(&self, to_type: LiteralType) -> Result<Self> {
        match self {
            Self::Address(address) => cast_group_to_type(address.to_group(), to_type),
            Self::Boolean(boolean) => cast_boolean_to_type(boolean, to_type),
            Self::Field(field) => cast_field_to_type(field, to_type),
            Self::Group(group) => cast_group_to_type(group, to_type),
            Self::I8(integer) => cast_integer_to_type(integer, to_type),
            Self::I16(integer) => cast_integer_to_type(integer, to_type),
            Self::I32(integer) => cast_integer_to_type(integer, to_type),
            Self::I64(integer) => cast_integer_to_type(integer, to_type),
            Self::I128(integer) => cast_integer_to_type(integer, to_type),
            Self::U8(integer) => cast_integer_to_type(integer, to_type),
            Self::U16(integer) => cast_integer_to_type(integer, to_type),
            Self::U32(integer) => cast_integer_to_type(integer, to_type),
            Self::U64(integer) => cast_integer_to_type(integer, to_type),
            Self::U128(integer) => cast_integer_to_type(integer, to_type),
            Self::Scalar(scalar) => cast_scalar_to_type(scalar, to_type),
            Self::Signature(..) => bail!("Cannot cast a signature literal to another type."),
            Self::String(..) => bail!("Cannot cast a string literal to another type."),
        }
    }

    /// Casts the literal to the given literal type, with lossy truncation.
    ///
    /// This method makes a *best-effort* attempt to preserve all bits of information,
    /// but it is not guaranteed to do so.
    ///
    /// The hierarchy of casting is as follows:
    ///  - (`Address`, `Group`) <-> `Field` <-> `Scalar` <-> `Integer` <-> `Boolean`
    ///  - `String` (not supported)
    /// Note that casting to left along the hierarchy always preserves information.
    pub fn cast_lossy(&self, to_type: LiteralType) -> Result<Self> {
        match self {
            Self::Address(address) => cast_lossy_group_to_type(address.to_group(), to_type),
            Self::Boolean(boolean) => cast_lossy_boolean_to_type(boolean, to_type),
            Self::Field(field) => cast_lossy_field_to_type(field, to_type),
            Self::Group(group) => cast_lossy_group_to_type(group, to_type),
            Self::I8(integer) => cast_lossy_integer_to_type(integer, to_type),
            Self::I16(integer) => cast_lossy_integer_to_type(integer, to_type),
            Self::I32(integer) => cast_lossy_integer_to_type(integer, to_type),
            Self::I64(integer) => cast_lossy_integer_to_type(integer, to_type),
            Self::I128(integer) => cast_lossy_integer_to_type(integer, to_type),
            Self::U8(integer) => cast_lossy_integer_to_type(integer, to_type),
            Self::U16(integer) => cast_lossy_integer_to_type(integer, to_type),
            Self::U32(integer) => cast_lossy_integer_to_type(integer, to_type),
            Self::U64(integer) => cast_lossy_integer_to_type(integer, to_type),
            Self::U128(integer) => cast_lossy_integer_to_type(integer, to_type),
            Self::Scalar(scalar) => cast_lossy_scalar_to_type(scalar, to_type),
            Self::Signature(..) => bail!("Cannot cast a signature literal to another type."),
            Self::String(..) => bail!("Cannot cast a string literal to another type."),
        }
    }
}

/// Casts a boolean literal to the given literal type.
fn cast_boolean_to_type<N: Network>(boolean: &Boolean<N>, to_type: LiteralType) -> Result<Literal<N>> {
    match to_type {
        LiteralType::Address => Ok(Literal::Address(boolean.cast()?)),
        LiteralType::Boolean => Ok(Literal::Boolean(*boolean)),
        LiteralType::Field => Ok(Literal::Field(boolean.cast()?)),
        LiteralType::Group => Ok(Literal::Group(boolean.cast()?)),
        LiteralType::I8 => Ok(Literal::I8(boolean.cast()?)),
        LiteralType::I16 => Ok(Literal::I16(boolean.cast()?)),
        LiteralType::I32 => Ok(Literal::I32(boolean.cast()?)),
        LiteralType::I64 => Ok(Literal::I64(boolean.cast()?)),
        LiteralType::I128 => Ok(Literal::I128(boolean.cast()?)),
        LiteralType::U8 => Ok(Literal::U8(boolean.cast()?)),
        LiteralType::U16 => Ok(Literal::U16(boolean.cast()?)),
        LiteralType::U32 => Ok(Literal::U32(boolean.cast()?)),
        LiteralType::U64 => Ok(Literal::U64(boolean.cast()?)),
        LiteralType::U128 => Ok(Literal::U128(boolean.cast()?)),
        LiteralType::Scalar => Ok(Literal::Scalar(boolean.cast()?)),
        LiteralType::Signature => bail!("Cannot cast a boolean literal to a signature type."),
        LiteralType::String => bail!("Cannot cast a boolean literal to a string type."),
    }
}

/// Casts a boolean literal to the given literal type, with lossy truncation.
fn cast_lossy_boolean_to_type<N: Network>(boolean: &Boolean<N>, to_type: LiteralType) -> Result<Literal<N>> {
    match to_type {
        LiteralType::Address => Ok(Literal::Address(boolean.cast_lossy()?)),
        LiteralType::Boolean => Ok(Literal::Boolean(*boolean)),
        LiteralType::Field => Ok(Literal::Field(boolean.cast_lossy()?)),
        LiteralType::Group => Ok(Literal::Group(boolean.cast_lossy()?)),
        LiteralType::I8 => Ok(Literal::I8(boolean.cast_lossy()?)),
        LiteralType::I16 => Ok(Literal::I16(boolean.cast_lossy()?)),
        LiteralType::I32 => Ok(Literal::I32(boolean.cast_lossy()?)),
        LiteralType::I64 => Ok(Literal::I64(boolean.cast_lossy()?)),
        LiteralType::I128 => Ok(Literal::I128(boolean.cast_lossy()?)),
        LiteralType::U8 => Ok(Literal::U8(boolean.cast_lossy()?)),
        LiteralType::U16 => Ok(Literal::U16(boolean.cast_lossy()?)),
        LiteralType::U32 => Ok(Literal::U32(boolean.cast_lossy()?)),
        LiteralType::U64 => Ok(Literal::U64(boolean.cast_lossy()?)),
        LiteralType::U128 => Ok(Literal::U128(boolean.cast_lossy()?)),
        LiteralType::Scalar => Ok(Literal::Scalar(boolean.cast_lossy()?)),
        LiteralType::Signature => bail!("Cannot cast a boolean literal to a signature type."),
        LiteralType::String => bail!("Cannot cast a boolean literal to a string type."),
    }
}

/// Casts a field literal to the given literal type.
fn cast_field_to_type<N: Network>(field: &Field<N>, to_type: LiteralType) -> Result<Literal<N>> {
    match to_type {
        LiteralType::Address => Ok(Literal::Address(field.cast()?)),
        LiteralType::Boolean => Ok(Literal::Boolean(field.cast()?)),
        LiteralType::Field => Ok(Literal::Field(*field)),
        LiteralType::Group => Ok(Literal::Group(field.cast()?)),
        LiteralType::I8 => Ok(Literal::I8(field.cast()?)),
        LiteralType::I16 => Ok(Literal::I16(field.cast()?)),
        LiteralType::I32 => Ok(Literal::I32(field.cast()?)),
        LiteralType::I64 => Ok(Literal::I64(field.cast()?)),
        LiteralType::I128 => Ok(Literal::I128(field.cast()?)),
        LiteralType::U8 => Ok(Literal::U8(field.cast()?)),
        LiteralType::U16 => Ok(Literal::U16(field.cast()?)),
        LiteralType::U32 => Ok(Literal::U32(field.cast()?)),
        LiteralType::U64 => Ok(Literal::U64(field.cast()?)),
        LiteralType::U128 => Ok(Literal::U128(field.cast()?)),
        LiteralType::Scalar => Ok(Literal::Scalar(field.cast()?)),
        LiteralType::Signature => bail!("Cannot cast a field literal to a signature type."),
        LiteralType::String => bail!("Cannot cast a field literal to a string type."),
    }
}

/// Casts a field literal to the given literal type, with lossy truncation.
fn cast_lossy_field_to_type<N: Network>(field: &Field<N>, to_type: LiteralType) -> Result<Literal<N>> {
    match to_type {
        LiteralType::Address => Ok(Literal::Address(field.cast_lossy()?)),
        LiteralType::Boolean => Ok(Literal::Boolean(field.cast_lossy()?)),
        LiteralType::Field => Ok(Literal::Field(*field)),
        LiteralType::Group => Ok(Literal::Group(field.cast_lossy()?)),
        LiteralType::I8 => Ok(Literal::I8(field.cast_lossy()?)),
        LiteralType::I16 => Ok(Literal::I16(field.cast_lossy()?)),
        LiteralType::I32 => Ok(Literal::I32(field.cast_lossy()?)),
        LiteralType::I64 => Ok(Literal::I64(field.cast_lossy()?)),
        LiteralType::I128 => Ok(Literal::I128(field.cast_lossy()?)),
        LiteralType::U8 => Ok(Literal::U8(field.cast_lossy()?)),
        LiteralType::U16 => Ok(Literal::U16(field.cast_lossy()?)),
        LiteralType::U32 => Ok(Literal::U32(field.cast_lossy()?)),
        LiteralType::U64 => Ok(Literal::U64(field.cast_lossy()?)),
        LiteralType::U128 => Ok(Literal::U128(field.cast_lossy()?)),
        LiteralType::Scalar => Ok(Literal::Scalar(field.cast_lossy()?)),
        LiteralType::Signature => bail!("Cannot cast a field literal to a signature type."),
        LiteralType::String => bail!("Cannot cast a field literal to a string type."),
    }
}

/// Casts a group literal to the given literal type.
fn cast_group_to_type<N: Network>(group: &Group<N>, to_type: LiteralType) -> Result<Literal<N>> {
    match to_type {
        LiteralType::Address => Ok(Literal::Address(Address::new(*group))),
        LiteralType::Group => Ok(Literal::Group(*group)),
        _ => cast_field_to_type(&group.to_x_coordinate(), to_type),
    }
}

/// Casts a group literal to the given literal type, with lossy truncation.
fn cast_lossy_group_to_type<N: Network>(group: &Group<N>, to_type: LiteralType) -> Result<Literal<N>> {
    match to_type {
        LiteralType::Address => Ok(Literal::Address(Address::new(*group))),
        LiteralType::Group => Ok(Literal::Group(*group)),
        _ => cast_lossy_field_to_type(&group.to_x_coordinate(), to_type),
    }
}

/// Casts an integer literal to the given literal type.
fn cast_integer_to_type<N: Network, I: IntegerType>(
    integer: &integers::Integer<N, I>,
    to_type: LiteralType,
) -> Result<Literal<N>>
where
    i8: TryFrom<I>,
    i16: TryFrom<I>,
    i32: TryFrom<I>,
    i64: TryFrom<I>,
    i128: TryFrom<I>,
    u8: TryFrom<I>,
    u16: TryFrom<I>,
    u32: TryFrom<I>,
    u64: TryFrom<I>,
    u128: TryFrom<I>,
{
    match to_type {
        LiteralType::Address => Ok(Literal::Address(integer.cast()?)),
        LiteralType::Boolean => Ok(Literal::Boolean(integer.cast()?)),
        LiteralType::Field => Ok(Literal::Field(integer.cast()?)),
        LiteralType::Group => Ok(Literal::Group(integer.cast()?)),
        LiteralType::I8 => Ok(Literal::I8(integer.cast()?)),
        LiteralType::I16 => Ok(Literal::I16(integer.cast()?)),
        LiteralType::I32 => Ok(Literal::I32(integer.cast()?)),
        LiteralType::I64 => Ok(Literal::I64(integer.cast()?)),
        LiteralType::I128 => Ok(Literal::I128(integer.cast()?)),
        LiteralType::U8 => Ok(Literal::U8(integer.cast()?)),
        LiteralType::U16 => Ok(Literal::U16(integer.cast()?)),
        LiteralType::U32 => Ok(Literal::U32(integer.cast()?)),
        LiteralType::U64 => Ok(Literal::U64(integer.cast()?)),
        LiteralType::U128 => Ok(Literal::U128(integer.cast()?)),
        LiteralType::Scalar => Ok(Literal::Scalar(integer.cast()?)),
        LiteralType::Signature => bail!("Cannot cast an integer literal to a signature type."),
        LiteralType::String => bail!("Cannot cast an integer literal to a string type."),
    }
}

/// Casts an integer literal to the given literal type, with lossy truncation.
fn cast_lossy_integer_to_type<N: Network, I: IntegerType>(
    integer: &integers::Integer<N, I>,
    to_type: LiteralType,
) -> Result<Literal<N>>
where
    I: AsPrimitive<u8>
        + AsPrimitive<u16>
        + AsPrimitive<u32>
        + AsPrimitive<u64>
        + AsPrimitive<u128>
        + AsPrimitive<i8>
        + AsPrimitive<i16>
        + AsPrimitive<i32>
        + AsPrimitive<i64>
        + AsPrimitive<i128>,
{
    match to_type {
        LiteralType::Address => Ok(Literal::Address(integer.cast_lossy()?)),
        LiteralType::Boolean => Ok(Literal::Boolean(integer.cast_lossy()?)),
        LiteralType::Field => Ok(Literal::Field(integer.cast_lossy()?)),
        LiteralType::Group => Ok(Literal::Group(integer.cast_lossy()?)),
        LiteralType::I8 => Ok(Literal::I8(integer.cast_lossy()?)),
        LiteralType::I16 => Ok(Literal::I16(integer.cast_lossy()?)),
        LiteralType::I32 => Ok(Literal::I32(integer.cast_lossy()?)),
        LiteralType::I64 => Ok(Literal::I64(integer.cast_lossy()?)),
        LiteralType::I128 => Ok(Literal::I128(integer.cast_lossy()?)),
        LiteralType::U8 => Ok(Literal::U8(integer.cast_lossy()?)),
        LiteralType::U16 => Ok(Literal::U16(integer.cast_lossy()?)),
        LiteralType::U32 => Ok(Literal::U32(integer.cast_lossy()?)),
        LiteralType::U64 => Ok(Literal::U64(integer.cast_lossy()?)),
        LiteralType::U128 => Ok(Literal::U128(integer.cast_lossy()?)),
        LiteralType::Scalar => Ok(Literal::Scalar(integer.cast_lossy()?)),
        LiteralType::Signature => bail!("Cannot cast an integer literal to a signature type."),
        LiteralType::String => bail!("Cannot cast an integer literal to a string type."),
    }
}

/// Casts a scalar literal to the given literal type.
fn cast_scalar_to_type<N: Network>(scalar: &Scalar<N>, to_type: LiteralType) -> Result<Literal<N>> {
    match to_type {
        LiteralType::Address => Ok(Literal::Address(scalar.cast()?)),
        LiteralType::Boolean => Ok(Literal::Boolean(scalar.cast()?)),
        LiteralType::Field => Ok(Literal::Field(scalar.cast()?)),
        LiteralType::Group => Ok(Literal::Group(scalar.cast()?)),
        LiteralType::I8 => Ok(Literal::I8(scalar.cast()?)),
        LiteralType::I16 => Ok(Literal::I16(scalar.cast()?)),
        LiteralType::I32 => Ok(Literal::I32(scalar.cast()?)),
        LiteralType::I64 => Ok(Literal::I64(scalar.cast()?)),
        LiteralType::I128 => Ok(Literal::I128(scalar.cast()?)),
        LiteralType::U8 => Ok(Literal::U8(scalar.cast()?)),
        LiteralType::U16 => Ok(Literal::U16(scalar.cast()?)),
        LiteralType::U32 => Ok(Literal::U32(scalar.cast()?)),
        LiteralType::U64 => Ok(Literal::U64(scalar.cast()?)),
        LiteralType::U128 => Ok(Literal::U128(scalar.cast()?)),
        LiteralType::Scalar => Ok(Literal::Scalar(*scalar)),
        LiteralType::Signature => bail!("Cannot cast a scalar literal to a signature type."),
        LiteralType::String => bail!("Cannot cast a scalar literal to a string type."),
    }
}

/// Casts a scalar literal to the given literal type, with lossy truncation.
fn cast_lossy_scalar_to_type<N: Network>(scalar: &Scalar<N>, to_type: LiteralType) -> Result<Literal<N>> {
    match to_type {
        LiteralType::Address => Ok(Literal::Address(scalar.cast_lossy()?)),
        LiteralType::Boolean => Ok(Literal::Boolean(scalar.cast_lossy()?)),
        LiteralType::Field => Ok(Literal::Field(scalar.cast_lossy()?)),
        LiteralType::Group => Ok(Literal::Group(scalar.cast_lossy()?)),
        LiteralType::I8 => Ok(Literal::I8(scalar.cast_lossy()?)),
        LiteralType::I16 => Ok(Literal::I16(scalar.cast_lossy()?)),
        LiteralType::I32 => Ok(Literal::I32(scalar.cast_lossy()?)),
        LiteralType::I64 => Ok(Literal::I64(scalar.cast_lossy()?)),
        LiteralType::I128 => Ok(Literal::I128(scalar.cast_lossy()?)),
        LiteralType::U8 => Ok(Literal::U8(scalar.cast_lossy()?)),
        LiteralType::U16 => Ok(Literal::U16(scalar.cast_lossy()?)),
        LiteralType::U32 => Ok(Literal::U32(scalar.cast_lossy()?)),
        LiteralType::U64 => Ok(Literal::U64(scalar.cast_lossy()?)),
        LiteralType::U128 => Ok(Literal::U128(scalar.cast_lossy()?)),
        LiteralType::Scalar => Ok(Literal::Scalar(*scalar)),
        LiteralType::Signature => bail!("Cannot cast a scalar literal to a signature type."),
        LiteralType::String => bail!("Cannot cast a scalar literal to a string type."),
    }
}
