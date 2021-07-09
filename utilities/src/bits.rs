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
    fn to_bits_le(&self) -> anyhow::Result<Vec<bool>>;
}

pub trait FromBits: Sized {
    /// Reads `Self` from `reader` as little-endian bits.
    fn from_bits_le(bits: &[bool]) -> Self;
}
