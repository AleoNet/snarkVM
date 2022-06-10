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

impl<E: Environment, I: IntegerType> Not for Integer<E, I> {
    type Output = Self;

    /// Returns the bitwise `NOT` of `self`.
    #[inline]
    fn not(self) -> Self::Output {
        Integer::new(self.integer.not())
    }
}

impl<E: Environment, I: IntegerType> BitAnd for Integer<E, I> {
    type Output = Self;

    /// Returns the bitwise `AND` of `self` and `other`.
    #[inline]
    fn bitand(self, other: Self) -> Self::Output {
        Integer::new(self.integer & other.integer)
    }
}

impl<E: Environment, I: IntegerType> BitAndAssign for Integer<E, I> {
    /// Performs the bitwise `AND` of `self` and `other` and assigns the result to `self`.
    #[inline]
    fn bitand_assign(&mut self, other: Self) {
        self.integer = self.integer & other.integer;
    }
}

impl<E: Environment, I: IntegerType> BitOr for Integer<E, I> {
    type Output = Self;

    /// Returns the bitwise `OR` of `self` and `other`.
    #[inline]
    fn bitor(self, other: Self) -> Self::Output {
        Integer::new(self.integer | other.integer)
    }
}

impl<E: Environment, I: IntegerType> BitOrAssign for Integer<E, I> {
    /// Performs the bitwise `OR` of `self` and `other` and assigns the result to `self`.
    #[inline]
    fn bitor_assign(&mut self, other: Self) {
        self.integer = self.integer | other.integer;
    }
}

impl<E: Environment, I: IntegerType> BitXor for Integer<E, I> {
    type Output = Self;

    /// Returns the bitwise `XOR` of `self` and `other`.
    #[inline]
    fn bitxor(self, other: Self) -> Self::Output {
        Integer::new(self.integer ^ other.integer)
    }
}

impl<E: Environment, I: IntegerType> BitXorAssign for Integer<E, I> {
    /// Performs the bitwise `XOR` of `self` and `other` and assigns the result to `self`.
    #[inline]
    fn bitxor_assign(&mut self, other: Self) {
        self.integer = self.integer ^ other.integer;
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> Shl<Integer<E, M>> for Integer<E, I> {
    type Output = Self;

    /// Shifts `self` to the left by `n` bits.
    #[inline]
    fn shl(self, n: Integer<E, M>) -> Self::Output {
        match self.integer.checked_shl(n.integer.to_u32().unwrap()) {
            // Unwrap is safe as we only cast up.
            Some(shifted) => Integer::new(shifted),
            None => E::halt(format!("Failed to shift {self} left by {n} bits")),
        }
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> ShlAssign<Integer<E, M>> for Integer<E, I> {
    /// Shifts `self` to the left by `n` bits and assigns the result to `self`.
    #[inline]
    fn shl_assign(&mut self, n: Integer<E, M>) {
        match self.integer.checked_shl(n.integer.to_u32().unwrap()) {
            // Unwrap is safe as we only cast up.
            Some(shifted) => {
                self.integer = shifted;
            }
            None => E::halt(format!("Failed to shift {self} left by {n} bits")),
        }
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> Shr<Integer<E, M>> for Integer<E, I> {
    type Output = Self;

    /// Shifts `self` to the right by `n` bits.
    #[inline]
    fn shr(self, n: Integer<E, M>) -> Self::Output {
        match self.integer.checked_shr(n.integer.to_u32().unwrap()) {
            // Unwrap is safe as we only cast up.
            Some(shifted) => Integer::new(shifted),
            None => E::halt(format!("Failed to shift {self} right by {n} bits")),
        }
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> ShrAssign<Integer<E, M>> for Integer<E, I> {
    /// Shifts `self` to the right by `n` bits and assigns the result to `self`.
    #[inline]
    fn shr_assign(&mut self, n: Integer<E, M>) {
        match self.integer.checked_shr(n.integer.to_u32().unwrap()) {
            // Unwrap is safe as we only cast up.
            Some(shifted) => {
                self.integer = shifted;
            }
            None => E::halt(format!("Failed to shift {self} right by {n} bits")),
        }
    }
}
