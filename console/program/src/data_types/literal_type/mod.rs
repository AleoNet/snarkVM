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

mod bytes;
mod parse;
mod serialize;
mod size_in_bits;
mod size_in_bytes;

use snarkvm_console_account::Signature;
use snarkvm_console_network::prelude::*;
use snarkvm_console_types::{prelude::*, Boolean};

use core::fmt::{self, Debug, Display};

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum LiteralType<N: Network> {
    /// The Aleo address type.
    Address,
    /// The boolean type.
    Boolean,
    /// The bytes type.
    Bytes(U32<N>),
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
    /// The signature type.
    Signature,
    /// The string type.
    String,
}

impl<N: Network> LiteralType<N> {
    /// Returns the unique numeric identifier for the literal type.
    pub fn type_id(&self) -> u8 {
        match &self {
            Self::Address => 0,
            Self::Boolean => 1,
            Self::Bytes(_) => 2,
            Self::Field => 3,
            Self::Group => 4,
            Self::I8 => 5,
            Self::I16 => 6,
            Self::I32 => 7,
            Self::I64 => 8,
            Self::I128 => 9,
            Self::U8 => 10,
            Self::U16 => 11,
            Self::U32 => 12,
            Self::U64 => 13,
            Self::U128 => 14,
            Self::Scalar => 15,
            Self::Signature => 16,
            Self::String => 17,
        }
    }
}
