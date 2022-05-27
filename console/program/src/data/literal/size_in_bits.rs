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
            Self::Address(..) => N::Field::size_in_bits() as u16,
            Self::Boolean(..) => 1u16,
            Self::Field(..) => N::Field::size_in_bits() as u16,
            Self::Group(..) => N::Field::size_in_bits() as u16,
            Self::I8(..) => i8::BITS as u16,
            Self::I16(..) => i16::BITS as u16,
            Self::I32(..) => i32::BITS as u16,
            Self::I64(..) => i64::BITS as u16,
            Self::I128(..) => i128::BITS as u16,
            Self::U8(..) => u8::BITS as u16,
            Self::U16(..) => u16::BITS as u16,
            Self::U32(..) => u32::BITS as u16,
            Self::U64(..) => u64::BITS as u16,
            Self::U128(..) => u128::BITS as u16,
            Self::Scalar(..) => N::Scalar::size_in_bits() as u16,
            Self::String(string) => (string.len() * 8) as u16,
        }
    }
}
