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
