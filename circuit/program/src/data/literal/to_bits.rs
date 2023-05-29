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

impl<A: Aleo> ToBits for Literal<A> {
    type Boolean = Boolean<A>;

    /// Returns the little-endian bits of the literal.
    fn to_bits_le(&self) -> Vec<Boolean<A>> {
        (&self).to_bits_le()
    }

    /// Returns the big-endian bits of the literal.
    fn to_bits_be(&self) -> Vec<Boolean<A>> {
        (&self).to_bits_be()
    }
}

impl<A: Aleo> ToBits for &Literal<A> {
    type Boolean = Boolean<A>;

    /// Returns the little-endian bits of the literal.
    fn to_bits_le(&self) -> Vec<Boolean<A>> {
        match self {
            Literal::Address(literal) => literal.to_bits_le(),
            Literal::Boolean(literal) => literal.to_bits_le(),
            Literal::Field(literal) => literal.to_bits_le(),
            Literal::Group(literal) => literal.to_bits_le(),
            Literal::I8(literal) => literal.to_bits_le(),
            Literal::I16(literal) => literal.to_bits_le(),
            Literal::I32(literal) => literal.to_bits_le(),
            Literal::I64(literal) => literal.to_bits_le(),
            Literal::I128(literal) => literal.to_bits_le(),
            Literal::U8(literal) => literal.to_bits_le(),
            Literal::U16(literal) => literal.to_bits_le(),
            Literal::U32(literal) => literal.to_bits_le(),
            Literal::U64(literal) => literal.to_bits_le(),
            Literal::U128(literal) => literal.to_bits_le(),
            Literal::Scalar(literal) => literal.to_bits_le(),
            Literal::String(literal) => literal.to_bits_le(),
        }
    }

    /// Returns the big-endian bits of the literal.
    fn to_bits_be(&self) -> Vec<Boolean<A>> {
        match self {
            Literal::Address(literal) => literal.to_bits_be(),
            Literal::Boolean(literal) => literal.to_bits_be(),
            Literal::Field(literal) => literal.to_bits_be(),
            Literal::Group(literal) => literal.to_bits_be(),
            Literal::I8(literal) => literal.to_bits_be(),
            Literal::I16(literal) => literal.to_bits_be(),
            Literal::I32(literal) => literal.to_bits_be(),
            Literal::I64(literal) => literal.to_bits_be(),
            Literal::I128(literal) => literal.to_bits_be(),
            Literal::U8(literal) => literal.to_bits_be(),
            Literal::U16(literal) => literal.to_bits_be(),
            Literal::U32(literal) => literal.to_bits_be(),
            Literal::U64(literal) => literal.to_bits_be(),
            Literal::U128(literal) => literal.to_bits_be(),
            Literal::Scalar(literal) => literal.to_bits_be(),
            Literal::String(literal) => literal.to_bits_be(),
        }
    }
}
