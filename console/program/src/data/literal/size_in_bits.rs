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

impl<N: Network> Literal<N> {
    /// Returns the number of bits of this literal.
    pub fn size_in_bits(&self) -> u16 {
        match self {
            Self::Address(..) => Address::<N>::size_in_bits() as u16,
            Self::Boolean(..) => Boolean::<N>::size_in_bits() as u16,
            Self::Field(..) => Field::<N>::size_in_bits() as u16,
            Self::Group(..) => Group::<N>::size_in_bits() as u16,
            Self::I8(..) => I8::<N>::size_in_bits() as u16,
            Self::I16(..) => I16::<N>::size_in_bits() as u16,
            Self::I32(..) => I32::<N>::size_in_bits() as u16,
            Self::I64(..) => I64::<N>::size_in_bits() as u16,
            Self::I128(..) => I128::<N>::size_in_bits() as u16,
            Self::U8(..) => U8::<N>::size_in_bits() as u16,
            Self::U16(..) => U16::<N>::size_in_bits() as u16,
            Self::U32(..) => U32::<N>::size_in_bits() as u16,
            Self::U64(..) => U64::<N>::size_in_bits() as u16,
            Self::U128(..) => U128::<N>::size_in_bits() as u16,
            Self::Scalar(..) => Scalar::<N>::size_in_bits() as u16,
            Self::String(string) => (string.len() * 8) as u16,
        }
    }
}
