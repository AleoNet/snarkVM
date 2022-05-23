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

impl<N: Network> FromBits for Identifier<N> {
    /// Initializes a new identifier from a list of little-endian bits *without* trailing zeros.
    fn from_bits_le(bits_le: &[bool]) -> Result<Self> {
        Self::from_str(&String::from_utf8(Vec::<u8>::from_bits_le(bits_le)?)?)
    }

    /// Initializes a new identifier from a list of big-endian bits *without* leading zeros.
    fn from_bits_be(bits_be: &[bool]) -> Result<Self> {
        Self::from_str(&String::from_utf8(Vec::<u8>::from_bits_be(bits_be)?)?)
    }
}
