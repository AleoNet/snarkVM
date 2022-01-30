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

impl<E: Environment, I: IntegerType> Div<Integer<E, I>> for Integer<E, I> {
    type Output = Self;

    fn div(self, other: Self) -> Self::Output {
        self / &other
    }
}

impl<E: Environment, I: IntegerType> Div<Integer<E, I>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn div(self, other: Integer<E, I>) -> Self::Output {
        self / &other
    }
}

impl<E: Environment, I: IntegerType> Div<&Integer<E, I>> for Integer<E, I> {
    type Output = Self;

    fn div(self, other: &Self) -> Self::Output {
        &self / other
    }
}

impl<E: Environment, I: IntegerType> Div<&Integer<E, I>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn div(self, other: &Integer<E, I>) -> Self::Output {
        let mut output = self.clone();
        output /= other;
        output
    }
}

impl<E: Environment, I: IntegerType> DivAssign<Integer<E, I>> for Integer<E, I> {
    fn div_assign(&mut self, other: Integer<E, I>) {
        *self /= &other;
    }
}

impl<E: Environment, I: IntegerType> DivAssign<&Integer<E, I>> for Integer<E, I> {
    fn div_assign(&mut self, other: &Integer<E, I>) {
        // Stores the quotient of `self` and `other` in `self`.
        *self = self.div_checked(other);
    }
}
