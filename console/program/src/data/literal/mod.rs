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
mod from_bits;
mod parse;
mod sample;
mod serialize;
mod size_in_bits;
mod to_bits;
mod to_type;
mod variant;

use crate::LiteralType;
use snarkvm_console_network::Network;
use snarkvm_console_types::{prelude::*, Boolean};

/// The literal enum represents all supported types in snarkVM.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Literal<N: Network> {
    /// The Aleo address type.
    Address(Address<N>),
    /// The boolean type.
    Boolean(Boolean<N>),
    /// The field type.
    Field(Field<N>),
    /// The group type.
    Group(Group<N>),
    /// The 8-bit signed integer type.
    I8(I8<N>),
    /// The 16-bit signed integer type.
    I16(I16<N>),
    /// The 32-bit signed integer type.
    I32(I32<N>),
    /// The 64-bit signed integer type.
    I64(I64<N>),
    /// The 128-bit signed integer type.
    I128(I128<N>),
    /// The 8-bit unsigned integer type.
    U8(U8<N>),
    /// The 16-bit unsigned integer type.
    U16(U16<N>),
    /// The 32-bit unsigned integer type.
    U32(U32<N>),
    /// The 64-bit unsigned integer type.
    U64(U64<N>),
    /// The 128-bit unsigned integer type.
    U128(U128<N>),
    /// The scalar type.
    Scalar(Scalar<N>),
    /// The string type.
    String(StringType<N>),
}
