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

impl<A: Aleo> Equal<Self> for Literal<A> {
    type Output = Boolean<A>;

    /// Returns `true` if `self` and `other` are equal.
    fn is_equal(&self, other: &Self) -> Self::Output {
        match (self, other) {
            (Self::Address(a), Self::Address(b)) => a.is_equal(b),
            (Self::Boolean(a), Self::Boolean(b)) => a.is_equal(b),
            (Self::Field(a), Self::Field(b)) => a.is_equal(b),
            (Self::Group(a), Self::Group(b)) => a.is_equal(b),
            (Self::I8(a), Self::I8(b)) => a.is_equal(b),
            (Self::I16(a), Self::I16(b)) => a.is_equal(b),
            (Self::I32(a), Self::I32(b)) => a.is_equal(b),
            (Self::I64(a), Self::I64(b)) => a.is_equal(b),
            (Self::I128(a), Self::I128(b)) => a.is_equal(b),
            (Self::U8(a), Self::U8(b)) => a.is_equal(b),
            (Self::U16(a), Self::U16(b)) => a.is_equal(b),
            (Self::U32(a), Self::U32(b)) => a.is_equal(b),
            (Self::U64(a), Self::U64(b)) => a.is_equal(b),
            (Self::U128(a), Self::U128(b)) => a.is_equal(b),
            (Self::Scalar(a), Self::Scalar(b)) => a.is_equal(b),
            (Self::String(a), Self::String(b)) => a.is_equal(b),
            _ => Boolean::constant(false),
        }
    }

    /// Returns `true` if `self` and `other` are *not* equal.
    fn is_not_equal(&self, other: &Self) -> Self::Output {
        match (self, other) {
            (Self::Address(a), Self::Address(b)) => a.is_not_equal(b),
            (Self::Boolean(a), Self::Boolean(b)) => a.is_not_equal(b),
            (Self::Field(a), Self::Field(b)) => a.is_not_equal(b),
            (Self::Group(a), Self::Group(b)) => a.is_not_equal(b),
            (Self::I8(a), Self::I8(b)) => a.is_not_equal(b),
            (Self::I16(a), Self::I16(b)) => a.is_not_equal(b),
            (Self::I32(a), Self::I32(b)) => a.is_not_equal(b),
            (Self::I64(a), Self::I64(b)) => a.is_not_equal(b),
            (Self::I128(a), Self::I128(b)) => a.is_not_equal(b),
            (Self::U8(a), Self::U8(b)) => a.is_not_equal(b),
            (Self::U16(a), Self::U16(b)) => a.is_not_equal(b),
            (Self::U32(a), Self::U32(b)) => a.is_not_equal(b),
            (Self::U64(a), Self::U64(b)) => a.is_not_equal(b),
            (Self::U128(a), Self::U128(b)) => a.is_not_equal(b),
            (Self::Scalar(a), Self::Scalar(b)) => a.is_not_equal(b),
            (Self::String(a), Self::String(b)) => a.is_not_equal(b),
            _ => Boolean::constant(true),
        }
    }
}
