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

use super::*;

impl<E: Environment, I: IntegerType, const BITS: usize> Add<Integer<E, I, BITS>> for Integer<E, I, BITS> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        self + &other
    }
}

impl<E: Environment, I: IntegerType, const BITS: usize> Add<Integer<E, I, BITS>> for &Integer<E, I, BITS> {
    type Output = Integer<E, I, BITS>;

    fn add(self, other: Integer<E, I, BITS>) -> Self::Output {
        self + &other
    }
}

impl<E: Environment, I: IntegerType, const BITS: usize> Add<&Integer<E, I, BITS>> for Integer<E, I, BITS> {
    type Output = Self;

    fn add(self, other: &Self) -> Self::Output {
        &self + other
    }
}

impl<E: Environment, I: IntegerType, const BITS: usize> Add<&Integer<E, I, BITS>> for &Integer<E, I, BITS> {
    type Output = Integer<E, I, BITS>;

    fn add(self, other: &Integer<E, I, BITS>) -> Self::Output {
        let mut output = self.clone();
        output += other;
        output
    }
}

impl<E: Environment, I: IntegerType, const BITS: usize> AddAssign<Integer<E, I, BITS>> for Integer<E, I, BITS> {
    fn add_assign(&mut self, other: Integer<E, I, BITS>) {
        *self += &other;
    }
}

impl<E: Environment, I: IntegerType, const BITS: usize> AddAssign<&Integer<E, I, BITS>> for Integer<E, I, BITS> {
    fn add_assign(&mut self, other: &Integer<E, I, BITS>) {
        // Stores the sum of `self` and `other` in `self`.
        *self = self.add_checked(other);
    }
}
