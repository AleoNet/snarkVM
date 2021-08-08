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

/// Takes as input a sequence of structs, and converts them to a series of little-endian bits.
/// All traits that implement `ToBits` can be automatically converted to bits in this manner.
#[macro_export]
macro_rules! to_bits_le {
    ($($x:expr),*) => ({
        let mut buffer = $crate::vec![];
        {$crate::push_bits_to_vec!(buffer, $($x),*)}.map(|_| buffer)
    });
}

#[macro_export]
macro_rules! push_bits_to_vec {
    ($buffer:expr, $y:expr, $($x:expr),*) => ({
        {ToBits::write_le(&$y, &mut $buffer)}.and({$crate::push_bits_to_vec!($buffer, $($x),*)})
    });

    ($buffer:expr, $x:expr) => ({
        ToBits::write_le(&$x, &mut $buffer)
    })
}

pub trait ToBits: Sized {
    /// Returns `self` as a boolean array in little-endian order.
    fn to_bits_le(&self) -> Vec<bool>;

    /// Returns `self` as a boolean array in big-endian order.
    fn to_bits_be(&self) -> Vec<bool>;
}

pub trait FromBits: Sized {
    /// Reads `Self` from a boolean array in little-endian order.
    fn from_bits_le(bits: &[bool]) -> Self;

    /// Reads `Self` from a boolean array in big-endian order.
    fn from_bits_be(bits: &[bool]) -> Self;
}

pub trait ToMinimalBitRepresentation: Sized {
    /// Returns `self` as a minimal boolean array.
    fn to_minimal_bit_representation(&self) -> Vec<bool>;
}

impl<T: ToMinimalBitRepresentation> ToMinimalBitRepresentation for Vec<T> {
    fn to_minimal_bit_representation(&self) -> Vec<bool> {
        let mut res_bits = vec![];
        for elem in self.iter() {
            res_bits.extend(elem.to_minimal_bit_representation());
        }
        res_bits
    }
}
