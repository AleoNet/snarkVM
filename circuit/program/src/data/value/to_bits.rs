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

impl<A: Aleo> ToBits for Value<A> {
    type Boolean = Boolean<A>;

    /// Returns the circuit value as a list of **little-endian** bits.
    #[inline]
    fn to_bits_le(&self) -> Vec<Boolean<A>> {
        match self {
            Self::Plaintext(plaintext) => plaintext.to_bits_le(),
            Self::Record(record) => record.to_bits_le(),
        }
    }

    /// Returns the circuit value as a list of **big-endian** bits.
    #[inline]
    fn to_bits_be(&self) -> Vec<Boolean<A>> {
        match self {
            Self::Plaintext(plaintext) => plaintext.to_bits_be(),
            Self::Record(record) => record.to_bits_be(),
        }
    }
}
