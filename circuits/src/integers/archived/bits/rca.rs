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

use crate::{Boolean, Environment, FullAdder, Mode};

use itertools::Itertools;

//TODO (@pranav) Reorganize where this code is kept
// Keeping here for now while prototyping.

/// Returns the bitwise sum of a n-bit number with carry bit
pub trait RippleCarryAdder<Rhs: ?Sized = Self> {
    fn add_bits(&self, other: &Rhs) -> Self;
}

// Generic impl
impl<E: Environment> RippleCarryAdder for Vec<Boolean<E>> {
    fn add_bits(&self, other: &Self) -> Self {
        let mut result = Vec::with_capacity(self.len() + 1);
        let mut carry = Boolean::new(Mode::Constant, false);

        for (a, b) in self.iter().zip_eq(other.iter()) {
            let (sum, next) = a.add_with_carry(b, &carry);

            carry = next;
            result.push(sum);
        }

        // append the carry bit to the end
        result.push(carry);

        result
    }
}
