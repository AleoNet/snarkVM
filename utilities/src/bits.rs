// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::Vec;
use bitvec::prelude::*;

pub trait ToBits: Sized {
    /// Returns `self` as a boolean array in little-endian order.
    fn to_bits_le(&self) -> BitVec<usize, Lsb0>;

    /// Returns `self` as a boolean array in big-endian order.
    fn to_bits_be(&self) -> BitVec<usize, Msb0>;
}

pub trait FromBits: Sized {
    /// Reads `Self` from a boolean array in little-endian order.
    fn from_bits_le(bits: &BitSlice<usize, Lsb0>) -> Self;

    /// Reads `Self` from a boolean array in big-endian order.
    fn from_bits_be(bits: &BitSlice<usize, Msb0>) -> Self;
}

pub trait ToMinimalBits: Sized {
    /// Returns `self` as a minimal boolean array.
    fn to_minimal_bits(&self) -> BitVec;
}

impl<T: ToMinimalBits> ToMinimalBits for Vec<T> {
    fn to_minimal_bits(&self) -> BitVec {
        let mut res_bits = BitVec::new();
        for elem in self.iter() {
            res_bits.extend(elem.to_minimal_bits());
        }
        res_bits
    }
}
