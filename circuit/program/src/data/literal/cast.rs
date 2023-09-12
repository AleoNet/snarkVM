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

impl<A: Aleo> Literal<A> {
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
            Self::Address(address) => cast_group_to_type(&address.to_group(), to_type),
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
            Self::Address(address) => cast_lossy_group_to_type(&address.to_group(), to_type),
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

// A helper macro to implement the `cast` and `cast_lossy` methods for each literal type.
macro_rules! impl_cast_to_type {
    ($type_:ty, $type_name:ident) => {
        paste::paste! {
            fn[<cast_ $type_name _to_type>]<A: Aleo>(input: &$type_, to_type: LiteralType) -> Result<Literal<A>> {
                match to_type {
                    LiteralType::Address => Ok(Literal::Address(input.cast())),
                    LiteralType::Boolean => Ok(Literal::Boolean(input.cast())),
                    LiteralType::Field => Ok(Literal::Field(input.cast())),
                    LiteralType::Group => Ok(Literal::Group(input.cast())),
                    LiteralType::I8 => Ok(Literal::I8(input.cast())),
                    LiteralType::I16 => Ok(Literal::I16(input.cast())),
                    LiteralType::I32 => Ok(Literal::I32(input.cast())),
                    LiteralType::I64 => Ok(Literal::I64(input.cast())),
                    LiteralType::I128 => Ok(Literal::I128(input.cast())),
                    LiteralType::U8 => Ok(Literal::U8(input.cast())),
                    LiteralType::U16 => Ok(Literal::U16(input.cast())),
                    LiteralType::U32 => Ok(Literal::U32(input.cast())),
                    LiteralType::U64 => Ok(Literal::U64(input.cast())),
                    LiteralType::U128 => Ok(Literal::U128(input.cast())),
                    LiteralType::Scalar => Ok(Literal::Scalar(input.cast())),
                    LiteralType::Signature => bail!(concat!("Cannot cast a ", stringify!($type_name), " literal to a signature type.")),
                    LiteralType::String => bail!(concat!("Cannot cast a ", stringify!($type_name), " literal to a string type.")),
                }
            }

            fn[<cast_lossy_ $type_name _to_type>]<A: Aleo>(input: &$type_, to_type: LiteralType) -> Result<Literal<A>> {
                match to_type {
                    LiteralType::Address => Ok(Literal::Address(input.cast_lossy())),
                    LiteralType::Boolean => Ok(Literal::Boolean(input.cast_lossy())),
                    LiteralType::Field => Ok(Literal::Field(input.cast_lossy())),
                    LiteralType::Group => Ok(Literal::Group(input.cast_lossy())),
                    LiteralType::I8 => Ok(Literal::I8(input.cast_lossy())),
                    LiteralType::I16 => Ok(Literal::I16(input.cast_lossy())),
                    LiteralType::I32 => Ok(Literal::I32(input.cast_lossy())),
                    LiteralType::I64 => Ok(Literal::I64(input.cast_lossy())),
                    LiteralType::I128 => Ok(Literal::I128(input.cast_lossy())),
                    LiteralType::U8 => Ok(Literal::U8(input.cast_lossy())),
                    LiteralType::U16 => Ok(Literal::U16(input.cast_lossy())),
                    LiteralType::U32 => Ok(Literal::U32(input.cast_lossy())),
                    LiteralType::U64 => Ok(Literal::U64(input.cast_lossy())),
                    LiteralType::U128 => Ok(Literal::U128(input.cast_lossy())),
                    LiteralType::Scalar => Ok(Literal::Scalar(input.cast_lossy())),
                    LiteralType::Signature => bail!(concat!("Cannot cast a ", stringify!($type_name), " literal to a signature type.")),
                    LiteralType::String => bail!(concat!("Cannot cast a ", stringify!($type_name), " literal to a string type.")),
                }
            }
        }
    }
}

impl_cast_to_type!(Boolean<A>, boolean);
impl_cast_to_type!(Field<A>, field);
impl_cast_to_type!(Scalar<A>, scalar);

/// Casts a group literal to the given literal type.
fn cast_group_to_type<A: Aleo>(group: &Group<A>, to_type: LiteralType) -> Result<Literal<A>> {
    match to_type {
        LiteralType::Address => Ok(Literal::Address(Address::from_group(group.clone()))),
        LiteralType::Group => Ok(Literal::Group(group.clone())),
        _ => cast_field_to_type(&group.to_x_coordinate(), to_type),
    }
}

/// Casts a group literal to the given literal type, with lossy truncation.
fn cast_lossy_group_to_type<A: Aleo>(group: &Group<A>, to_type: LiteralType) -> Result<Literal<A>> {
    match to_type {
        LiteralType::Address => Ok(Literal::Address(Address::from_group(group.clone()))),
        LiteralType::Group => Ok(Literal::Group(group.clone())),
        _ => cast_lossy_field_to_type(&group.to_x_coordinate(), to_type),
    }
}

/// Casts an integer literal to the given literal type.
fn cast_integer_to_type<A: Aleo, I: IntegerType>(
    integer: &integers::Integer<A, I>,
    to_type: LiteralType,
) -> Result<Literal<A>> {
    match to_type {
        LiteralType::Address => Ok(Literal::Address(integer.cast())),
        LiteralType::Boolean => Ok(Literal::Boolean(integer.cast())),
        LiteralType::Field => Ok(Literal::Field(integer.cast())),
        LiteralType::Group => Ok(Literal::Group(integer.cast())),
        LiteralType::I8 => Ok(Literal::I8(integer.cast())),
        LiteralType::I16 => Ok(Literal::I16(integer.cast())),
        LiteralType::I32 => Ok(Literal::I32(integer.cast())),
        LiteralType::I64 => Ok(Literal::I64(integer.cast())),
        LiteralType::I128 => Ok(Literal::I128(integer.cast())),
        LiteralType::U8 => Ok(Literal::U8(integer.cast())),
        LiteralType::U16 => Ok(Literal::U16(integer.cast())),
        LiteralType::U32 => Ok(Literal::U32(integer.cast())),
        LiteralType::U64 => Ok(Literal::U64(integer.cast())),
        LiteralType::U128 => Ok(Literal::U128(integer.cast())),
        LiteralType::Scalar => Ok(Literal::Scalar(integer.cast())),
        LiteralType::Signature => bail!("Cannot cast an integer literal to a signature type."),
        LiteralType::String => bail!("Cannot cast an integer literal to a string type."),
    }
}

/// Casts an integer literal to the given literal type, with lossy truncation.
fn cast_lossy_integer_to_type<A: Aleo, I: IntegerType>(
    integer: &integers::Integer<A, I>,
    to_type: LiteralType,
) -> Result<Literal<A>> {
    match to_type {
        LiteralType::Address => Ok(Literal::Address(integer.cast_lossy())),
        LiteralType::Boolean => Ok(Literal::Boolean(integer.cast_lossy())),
        LiteralType::Field => Ok(Literal::Field(integer.cast_lossy())),
        LiteralType::Group => Ok(Literal::Group(integer.cast_lossy())),
        LiteralType::I8 => Ok(Literal::I8(integer.cast_lossy())),
        LiteralType::I16 => Ok(Literal::I16(integer.cast_lossy())),
        LiteralType::I32 => Ok(Literal::I32(integer.cast_lossy())),
        LiteralType::I64 => Ok(Literal::I64(integer.cast_lossy())),
        LiteralType::I128 => Ok(Literal::I128(integer.cast_lossy())),
        LiteralType::U8 => Ok(Literal::U8(integer.cast_lossy())),
        LiteralType::U16 => Ok(Literal::U16(integer.cast_lossy())),
        LiteralType::U32 => Ok(Literal::U32(integer.cast_lossy())),
        LiteralType::U64 => Ok(Literal::U64(integer.cast_lossy())),
        LiteralType::U128 => Ok(Literal::U128(integer.cast_lossy())),
        LiteralType::Scalar => Ok(Literal::Scalar(integer.cast_lossy())),
        LiteralType::Signature => bail!("Cannot cast an integer literal to a signature type."),
        LiteralType::String => bail!("Cannot cast an integer literal to a string type."),
    }
}
