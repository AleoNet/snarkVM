// Copyright (C) 2019-2023 Aleo Systems Inc.
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

pub mod adder;
pub mod from_bits;
pub mod subtractor;
pub mod to_bits;

impl<E: Environment> Boolean<E> {
    /// Checks that the bitwise representation of a primitive datatype is less than or equal to the bitwise representation of a fixed value.
    /// This function assumes that the `circuit_bits_le` and `fixed_bits_le` are in little-endian order and are equal length.
    pub fn check_bits_le_less_than_or_equal(circuit_bits_le: &[Boolean<E>], fixed_bits_le: &[bool]) {
        // Compute `!(value < bits_le)`, which is equivalent to `value >= bits_le`.
        let is_less_than_or_equal_to_value = !fixed_bits_le.iter().zip_eq(circuit_bits_le).fold(
            Boolean::constant(false),
            |rest_is_less, (this, that)| {
                if *this { that.bitand(&rest_is_less) } else { that.bitor(&rest_is_less) }
            },
        );

        // Ensure that the non-unique bit-representation is less than or equal to the bitwise representation of `value`.
        E::assert(is_less_than_or_equal_to_value);
    }
}
