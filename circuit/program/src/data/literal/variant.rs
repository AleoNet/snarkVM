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
        U8::constant(match self {
            Self::Address(..) => console::U8::new(0),
            Self::Boolean(..) => console::U8::new(1),
            Self::Field(..) => console::U8::new(2),
            Self::Group(..) => console::U8::new(3),
            Self::I8(..) => console::U8::new(4),
            Self::I16(..) => console::U8::new(5),
            Self::I32(..) => console::U8::new(6),
            Self::I64(..) => console::U8::new(7),
            Self::I128(..) => console::U8::new(8),
            Self::U8(..) => console::U8::new(9),
            Self::U16(..) => console::U8::new(10),
            Self::U32(..) => console::U8::new(11),
            Self::U64(..) => console::U8::new(12),
            Self::U128(..) => console::U8::new(13),
            Self::Scalar(..) => console::U8::new(14),
            Self::String(..) => console::U8::new(15),
        })
    }
}
