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

impl<N: Network, I: IntegerType> Neg for Integer<N, I> {
    type Output = Integer<N, I>;

    /// Returns the `negation` of `self`.
    #[inline]
    fn neg(self) -> Self::Output {
        match I::is_signed() {
            true => match self.integer.checked_neg() {
                Some(integer) => Integer::new(self.mode, integer),
                None => N::halt(format!("Integer negation failed on: {}", self.integer)),
            },
            false => N::halt("Negation of unsigned integers is not supported."),
        }
    }
}

impl<N: Network, I: IntegerType> Add<Integer<N, I>> for Integer<N, I> {
    type Output = Integer<N, I>;

    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn add(self, other: Integer<N, I>) -> Self::Output {
        match self.integer.checked_add(&other.integer) {
            Some(integer) => Integer::new(self.mode, integer),
            None => N::halt(format!("Integer addition failed on: {} and {}", self.integer, other.integer)),
        }
    }
}

impl<N: Network, I: IntegerType> AddAssign<Integer<N, I>> for Integer<N, I> {
    /// Adds `other` to `self`.
    #[inline]
    fn add_assign(&mut self, other: Integer<N, I>) {
        match self.integer.checked_add(&other.integer) {
            Some(integer) => self.integer = integer,
            None => N::halt(format!("Integer addition failed on: {} and {}", self.integer, other.integer)),
        }
    }
}

impl<N: Network, I: IntegerType> Sub<Integer<N, I>> for Integer<N, I> {
    type Output = Integer<N, I>;

    /// Returns the `difference` of `self` and `other`.
    #[inline]
    fn sub(self, other: Integer<N, I>) -> Self::Output {
        match self.integer.checked_sub(&other.integer) {
            Some(integer) => Integer::new(self.mode, integer),
            None => N::halt(format!("Integer subtraction failed on: {} and {}", self.integer, other.integer)),
        }
    }
}

impl<N: Network, I: IntegerType> SubAssign<Integer<N, I>> for Integer<N, I> {
    /// Subtracts `other` from `self`.
    #[inline]
    fn sub_assign(&mut self, other: Integer<N, I>) {
        match self.integer.checked_sub(&other.integer) {
            Some(integer) => self.integer = integer,
            None => N::halt(format!("Integer subtraction failed on: {} and {}", self.integer, other.integer)),
        }
    }
}

impl<N: Network, I: IntegerType> Mul<Integer<N, I>> for Integer<N, I> {
    type Output = Integer<N, I>;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul(self, other: Integer<N, I>) -> Self::Output {
        match self.integer.checked_mul(&other.integer) {
            Some(integer) => Integer::new(self.mode, integer),
            None => N::halt(format!("Integer multiplication failed on: {} and {}", self.integer, other.integer)),
        }
    }
}

impl<N: Network, I: IntegerType> MulAssign<Integer<N, I>> for Integer<N, I> {
    /// Multiplies `self` by `other`.
    #[inline]
    fn mul_assign(&mut self, other: Integer<N, I>) {
        match self.integer.checked_mul(&other.integer) {
            Some(integer) => self.integer = integer,
            None => N::halt(format!("Integer multiplication failed on: {} and {}", self.integer, other.integer)),
        }
    }
}

impl<N: Network, I: IntegerType> Div<Integer<N, I>> for Integer<N, I> {
    type Output = Integer<N, I>;

    /// Returns the `quotient` of `self` and `other`.
    #[inline]
    fn div(self, other: Integer<N, I>) -> Self::Output {
        match self.integer.checked_div(&other.integer) {
            Some(integer) => Integer::new(self.mode, integer),
            None => N::halt(format!("Integer division failed on: {} and {}", self.integer, other.integer)),
        }
    }
}

impl<N: Network, I: IntegerType> DivAssign<Integer<N, I>> for Integer<N, I> {
    /// Divides `self` by `other`.
    #[inline]
    fn div_assign(&mut self, other: Integer<N, I>) {
        match self.integer.checked_div(&other.integer) {
            Some(integer) => self.integer = integer,
            None => N::halt(format!("Integer division failed on: {} and {}", self.integer, other.integer)),
        }
    }
}

impl<N: Network, I: IntegerType, M: Magnitude> Pow<Integer<N, M>> for Integer<N, I> {
    type Output = Integer<N, I>;

    /// Returns the `power` of `self` to the power of `other`.
    #[inline]
    fn pow(self, other: Integer<N, M>) -> Self::Output {
        match self.integer.checked_pow(&other.integer.to_u32().unwrap()) {
            // Unwrap is safe as we only cast up.
            Some(integer) => Integer::new(self.mode, integer),
            None => N::halt(format!("Integer power failed on: {} and {}", self.integer, other.integer)),
        }
    }
}

impl<N: Network, I: IntegerType> Square for Integer<N, I> {
    type Output = Integer<N, I>;

    /// Returns the `square` of `self`.
    #[inline]
    fn square(&self) -> Self::Output {
        match self.integer.checked_mul(&self.integer) {
            Some(integer) => Integer::new(self.mode, integer),
            None => N::halt(format!("Integer square failed on: {}", self.integer)),
        }
    }
}
