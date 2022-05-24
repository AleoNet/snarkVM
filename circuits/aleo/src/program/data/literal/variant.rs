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

impl<A: Aleo> Literal<A> {
    /// Returns the variant of the literal.
    pub fn variant(&self) -> U8<A> {
        match self {
            Self::Address(..) => U8::constant(0),
            Self::Boolean(..) => U8::constant(1),
            Self::Field(..) => U8::constant(2),
            Self::Group(..) => U8::constant(3),
            Self::I8(..) => U8::constant(4),
            Self::I16(..) => U8::constant(5),
            Self::I32(..) => U8::constant(6),
            Self::I64(..) => U8::constant(7),
            Self::I128(..) => U8::constant(8),
            Self::U8(..) => U8::constant(9),
            Self::U16(..) => U8::constant(10),
            Self::U32(..) => U8::constant(11),
            Self::U64(..) => U8::constant(12),
            Self::U128(..) => U8::constant(13),
            Self::Scalar(..) => U8::constant(14),
            Self::String(..) => U8::constant(15),
        }
    }
}
