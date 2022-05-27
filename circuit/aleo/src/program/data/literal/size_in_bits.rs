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
        U16::constant(match self {
            Self::Address(..) => A::BaseField::size_in_bits() as u16,
            Self::Boolean(..) => 1u16,
            Self::Field(..) => A::BaseField::size_in_bits() as u16,
            Self::Group(..) => A::BaseField::size_in_bits() as u16,
            Self::I8(..) => I8::<A>::size_in_bits(),
            Self::I16(..) => I16::<A>::size_in_bits(),
            Self::I32(..) => I32::<A>::size_in_bits(),
            Self::I64(..) => I64::<A>::size_in_bits(),
            Self::I128(..) => I128::<A>::size_in_bits(),
            Self::U8(..) => U8::<A>::size_in_bits(),
            Self::U16(..) => U16::<A>::size_in_bits(),
            Self::U32(..) => U32::<A>::size_in_bits(),
            Self::U64(..) => U64::<A>::size_in_bits(),
            Self::U128(..) => U128::<A>::size_in_bits(),
            Self::Scalar(..) => A::ScalarField::size_in_bits() as u16,
            Self::String(string) => string.to_bits_le().len() as u16,
        })
    }
}
