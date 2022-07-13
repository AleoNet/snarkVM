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

mod bytes;
mod parse;
mod serialize;

use snarkvm_console_network::prelude::*;

use core::fmt::{self, Debug, Display};
use num_derive::FromPrimitive;
use num_traits::FromPrimitive;

#[derive(Copy, Clone, PartialEq, Eq, Hash, FromPrimitive)]
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

impl LiteralType {
    /// Returns the literal type name.
    pub fn type_name(&self) -> &str {
        match self {
            Self::Address => "address",
            Self::Boolean => "boolean",
            Self::Field => "field",
            Self::Group => "group",
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::I128 => "i128",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::U128 => "u128",
            Self::Scalar => "scalar",
            Self::String => "string",
        }
    }
}
