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

mod boolean;
mod field;
mod integer;
mod scalar;

use crate::prelude::{
    bail,
    Address,
    BitOr,
    Boolean,
    Environment,
    Field,
    FromBits,
    FromBoolean,
    FromField,
    Group,
    IntegerType,
    One,
    Result,
    Scalar,
    SizeInBits,
    Ternary,
    ToBits,
    ToField,
    Zero,
    I128,
    I16,
    I32,
    I64,
    I8,
    U128,
    U16,
    U32,
    U64,
    U8,
};
use snarkvm_circuit_types_integers::Integer;

/// Unary operator for casting values of one type to another.
pub trait Cast<T: Sized = Self> {
    /// Casts the value of `self` into a value of type `T`.
    ///
    /// This method checks that the cast does not lose any bits of information.
    fn cast(&self) -> T;
}
