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
    /// Returns the number of bits of this literal.
    pub fn size_in_bits(&self) -> U16<A> {
        U16::constant(console::U16::new(match self {
            Self::Address(..) => console::Address::<A::Network>::size_in_bits() as u16,
            Self::Boolean(..) => console::Boolean::<A::Network>::size_in_bits() as u16,
            Self::Field(..) => console::Field::<A::Network>::size_in_bits() as u16,
            Self::Group(..) => console::Group::<A::Network>::size_in_bits() as u16,
            Self::I8(..) => console::I8::<A::Network>::size_in_bits() as u16,
            Self::I16(..) => console::I16::<A::Network>::size_in_bits() as u16,
            Self::I32(..) => console::I32::<A::Network>::size_in_bits() as u16,
            Self::I64(..) => console::I64::<A::Network>::size_in_bits() as u16,
            Self::I128(..) => console::I128::<A::Network>::size_in_bits() as u16,
            Self::U8(..) => console::U8::<A::Network>::size_in_bits() as u16,
            Self::U16(..) => console::U16::<A::Network>::size_in_bits() as u16,
            Self::U32(..) => console::U32::<A::Network>::size_in_bits() as u16,
            Self::U64(..) => console::U64::<A::Network>::size_in_bits() as u16,
            Self::U128(..) => console::U128::<A::Network>::size_in_bits() as u16,
            Self::Scalar(..) => console::Scalar::<A::Network>::size_in_bits() as u16,
            Self::String(string) => string.to_bits_le().len() as u16,
        }))
    }
}
