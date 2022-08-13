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

impl<A: Aleo> Equal<Self> for Ciphertext<A> {
    type Output = Boolean<A>;

    /// Returns `true` if `self` and `other` are equal.
    fn is_equal(&self, other: &Self) -> Self::Output {
        // Check each field element for equality.
        let mut equal = Boolean::constant(true);
        for (a, b) in self.0.iter().zip_eq(other.0.iter()) {
            equal &= a.is_equal(b);
        }
        equal
    }

    /// Returns `true` if `self` and `other` are *not* equal.
    fn is_not_equal(&self, other: &Self) -> Self::Output {
        // Recursively check each member for inequality.
        let mut not_equal = Boolean::constant(false);
        for (a, b) in self.0.iter().zip_eq(other.0.iter()) {
            not_equal |= a.is_not_equal(b);
        }
        not_equal
    }
}
