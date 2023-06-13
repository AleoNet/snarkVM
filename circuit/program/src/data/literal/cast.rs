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
use snarkvm_circuit_types::integers::Integer;

impl<A: Aleo> Literal<A> {
    /// Casts the literal to the given literal type.
    ///
    /// This method checks that the cast does not lose any bits of information,
    /// and returns an error if it does.
    ///
    /// The hierarchy of downcasting is as follows:
    ///  - (`Address`, `Group`) -> `Field` -> `Scalar` -> `Integer` -> `Boolean`
    ///  - `String` (not supported)
    ///
    /// The hierarchy of upcasting is the inverse of the downcasting hierarchy.
    pub fn cast(&self, to_type: LiteralType) -> Result<Self> {
        match self {
            Self::Address(address) => cast_group_to_type(address.to_group(), to_type),
            Self::Boolean(boolean) => cast_boolean_to_type(boolean.clone(), to_type),
            Self::Field(field) => cast_field_to_type(field.clone(), to_type),
            Self::Group(group) => cast_group_to_type(group.clone(), to_type),
            Self::I8(i8) => cast_integer_to_type(i8.clone(), to_type),
            Self::I16(i16) => cast_integer_to_type(i16.clone(), to_type),
            Self::I32(i32) => cast_integer_to_type(i32.clone(), to_type),
            Self::I64(i64) => cast_integer_to_type(i64.clone(), to_type),
            Self::I128(i128) => cast_integer_to_type(i128.clone(), to_type),
            Self::U8(u8) => cast_integer_to_type(u8.clone(), to_type),
            Self::U16(u16) => cast_integer_to_type(u16.clone(), to_type),
            Self::U32(u32) => cast_integer_to_type(u32.clone(), to_type),
            Self::U64(u64) => cast_integer_to_type(u64.clone(), to_type),
            Self::U128(u128) => cast_integer_to_type(u128.clone(), to_type),
            Self::Scalar(scalar) => cast_scalar_to_type(scalar.clone(), to_type),
            Self::String(..) => bail!("Cannot cast a string literal to another type."),
        }
    }

    /// Casts the literal to the given literal type, with lossy truncation.
    ///
    /// This method makes a *best-effort* attempt to preserve upcasting back
    /// to the original literal type, but it is not guaranteed to do so.
    ///
    /// The hierarchy of downcasting is as follows:
    ///  - (`Address`, `Group`) -> `Field` -> `Scalar` -> `Integer` -> `Boolean`
    ///  - `String` (not supported)
    ///
    /// The hierarchy of upcasting is the inverse of the downcasting hierarchy.
    pub fn cast_lossy(&self, to_type: LiteralType) -> Result<Self> {
        match self {
            Self::Address(address) => cast_lossy_group_to_type(address.to_group(), to_type),
            Self::Boolean(boolean) => cast_lossy_boolean_to_type(boolean.clone(), to_type),
            Self::Field(field) => cast_lossy_field_to_type(field.clone(), to_type),
            Self::Group(group) => cast_lossy_group_to_type(group.clone(), to_type),
            Self::I8(i8) => cast_lossy_integer_to_type(i8.clone(), to_type),
            Self::I16(i16) => cast_lossy_integer_to_type(i16.clone(), to_type),
            Self::I32(i32) => cast_lossy_integer_to_type(i32.clone(), to_type),
            Self::I64(i64) => cast_lossy_integer_to_type(i64.clone(), to_type),
            Self::I128(i128) => cast_lossy_integer_to_type(i128.clone(), to_type),
            Self::U8(u8) => cast_lossy_integer_to_type(u8.clone(), to_type),
            Self::U16(u16) => cast_lossy_integer_to_type(u16.clone(), to_type),
            Self::U32(u32) => cast_lossy_integer_to_type(u32.clone(), to_type),
            Self::U64(u64) => cast_lossy_integer_to_type(u64.clone(), to_type),
            Self::U128(u128) => cast_lossy_integer_to_type(u128.clone(), to_type),
            Self::Scalar(scalar) => cast_lossy_scalar_to_type(scalar.clone(), to_type),
            Self::String(..) => bail!("Cannot lossily cast a string literal to another type."),
        }
    }
}

/// Casts a boolean literal to the given literal type.
fn cast_boolean_to_type<A: Aleo>(boolean: Boolean<A>, to_type: LiteralType) -> Result<Literal<A>> {
    match to_type {
        LiteralType::Boolean => Ok(Literal::Boolean(boolean)),
        _ => cast_field_to_type(Field::from_bits_le(&boolean.to_bits_le()), to_type),
    }
}

/// Casts a boolean literal to the given literal type, with lossy truncation.
fn cast_lossy_boolean_to_type<A: Aleo>(boolean: Boolean<A>, to_type: LiteralType) -> Result<Literal<A>> {
    match to_type {
        LiteralType::Boolean => Ok(Literal::Boolean(boolean)),
        _ => cast_lossy_field_to_type(Field::from_bits_le(&boolean.to_bits_le()), to_type),
    }
}

/// Casts a field literal to the given literal type.
fn cast_field_to_type<A: Aleo>(field: Field<A>, to_type: LiteralType) -> Result<Literal<A>> {
    match to_type {
        LiteralType::Address => Ok(Literal::Address(Address::from_field(field))),
        LiteralType::Boolean => {
            // Convert the field element into bits.
            let bits_le = field.to_bits_le();
            // Ensure the upper bits are all zero.
            for bit in &bits_le[1..] {
                A::assert(!bit);
            }
            Ok(Literal::Boolean(bits_le[0].clone()))
        }
        LiteralType::Field => Ok(Literal::Field(field)),
        LiteralType::Group => Ok(Literal::Group(Group::from_x_coordinate(field))),
        LiteralType::I8 => Ok(Literal::I8(I8::from_field(field))),
        LiteralType::I16 => Ok(Literal::I16(I16::from_field(field))),
        LiteralType::I32 => Ok(Literal::I32(I32::from_field(field))),
        LiteralType::I64 => Ok(Literal::I64(I64::from_field(field))),
        LiteralType::I128 => Ok(Literal::I128(I128::from_field(field))),
        LiteralType::U8 => Ok(Literal::U8(U8::from_field(field))),
        LiteralType::U16 => Ok(Literal::U16(U16::from_field(field))),
        LiteralType::U32 => Ok(Literal::U32(U32::from_field(field))),
        LiteralType::U64 => Ok(Literal::U64(U64::from_field(field))),
        LiteralType::U128 => Ok(Literal::U128(U128::from_field(field))),
        LiteralType::Scalar => Ok(Literal::Scalar(Scalar::from_field(field))),
        LiteralType::String => bail!("Cannot cast a field literal to a string type."),
    }
}

/// Casts a field literal to the given literal type, with lossy truncation.
fn cast_lossy_field_to_type<A: Aleo>(field: Field<A>, to_type: LiteralType) -> Result<Literal<A>> {
    match to_type {
        LiteralType::Address => Ok(Literal::Address(Address::from_field(field))),
        LiteralType::Boolean => {
            // Convert the field element into bits.
            let bits_le = field.to_bits_le();
            // Convert the lower bit into a boolean.
            Ok(Literal::Boolean(bits_le[0].clone()))
        }
        LiteralType::Field => Ok(Literal::Field(field)),
        LiteralType::Group => Ok(Literal::Group(Group::from_x_coordinate(field))),
        LiteralType::I8 => Ok(Literal::I8(I8::from_field_lossy(field))),
        LiteralType::I16 => Ok(Literal::I16(I16::from_field_lossy(field))),
        LiteralType::I32 => Ok(Literal::I32(I32::from_field_lossy(field))),
        LiteralType::I64 => Ok(Literal::I64(I64::from_field_lossy(field))),
        LiteralType::I128 => Ok(Literal::I128(I128::from_field_lossy(field))),
        LiteralType::U8 => Ok(Literal::U8(U8::from_field_lossy(field))),
        LiteralType::U16 => Ok(Literal::U16(U16::from_field_lossy(field))),
        LiteralType::U32 => Ok(Literal::U32(U32::from_field_lossy(field))),
        LiteralType::U64 => Ok(Literal::U64(U64::from_field_lossy(field))),
        LiteralType::U128 => Ok(Literal::U128(U128::from_field_lossy(field))),
        LiteralType::Scalar => Ok(Literal::Scalar(Scalar::from_field_lossy(field))),
        LiteralType::String => bail!("Cannot lossily cast a field literal to a string type."),
    }
}

/// Casts a group literal to the given literal type.
fn cast_group_to_type<A: Aleo>(group: Group<A>, to_type: LiteralType) -> Result<Literal<A>> {
    match to_type {
        LiteralType::Address => Ok(Literal::Address(Address::from_group(group))),
        LiteralType::Group => Ok(Literal::Group(group)),
        _ => cast_field_to_type(group.to_x_coordinate(), to_type),
    }
}

/// Casts a group literal to the given literal type, with lossy truncation.
fn cast_lossy_group_to_type<A: Aleo>(group: Group<A>, to_type: LiteralType) -> Result<Literal<A>> {
    match to_type {
        LiteralType::Address => Ok(Literal::Address(Address::from_group(group))),
        LiteralType::Group => Ok(Literal::Group(group)),
        _ => cast_lossy_field_to_type(group.to_x_coordinate(), to_type),
    }
}

/// Casts an integer literal to the given literal type.
fn cast_integer_to_type<A: Aleo, I: IntegerType>(integer: Integer<A, I>, to_type: LiteralType) -> Result<Literal<A>> {
    cast_field_to_type(integer.to_field(), to_type)
}

/// Casts an integer literal to the given literal type, with lossy truncation.
fn cast_lossy_integer_to_type<A: Aleo, I: IntegerType>(
    integer: Integer<A, I>,
    to_type: LiteralType,
) -> Result<Literal<A>> {
    cast_lossy_field_to_type(integer.to_field(), to_type)
}

/// Casts a scalar literal to the given literal type.
fn cast_scalar_to_type<A: Aleo>(scalar: Scalar<A>, to_type: LiteralType) -> Result<Literal<A>> {
    match to_type {
        LiteralType::Scalar => Ok(Literal::Scalar(scalar)),
        _ => cast_field_to_type(scalar.to_field(), to_type),
    }
}

/// Casts a scalar literal to the given literal type, with lossy truncation.
fn cast_lossy_scalar_to_type<A: Aleo>(scalar: Scalar<A>, to_type: LiteralType) -> Result<Literal<A>> {
    match to_type {
        LiteralType::Scalar => Ok(Literal::Scalar(scalar)),
        _ => cast_lossy_field_to_type(scalar.to_field(), to_type),
    }
}
