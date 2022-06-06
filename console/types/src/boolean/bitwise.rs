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

impl<N: Network> Not for Boolean<N> {
    type Output = Boolean<N>;

    /// Returns the `negation` of `self`.
    #[inline]
    fn not(self) -> Self::Output {
        Boolean::new(self.mode, !self.boolean)
    }
}

impl<N: Network> BitAnd for Boolean<N> {
    type Output = Boolean<N>;

    /// Returns the bitwise `AND`` of `self` and `other`.
    #[inline]
    fn bitand(self, other: Self) -> Self::Output {
        Boolean::new(Mode::combine(self.mode, other.mode), self.boolean & other.boolean)
    }
}

impl<N: Network> BitAndAssign for Boolean<N> {
    /// Sets `self` as the bitwise `AND` of `self` and `other`.
    #[inline]
    fn bitand_assign(&mut self, other: Self) {
        *self = Boolean::new(Mode::combine(self.mode, other.mode), self.boolean & other.boolean)
    }
}

impl<N: Network> BitOr for Boolean<N> {
    type Output = Boolean<N>;

    /// Returns the bitwise `OR` of `self` and `other`.
    #[inline]
    fn bitor(self, other: Self) -> Self::Output {
        Boolean::new(Mode::combine(self.mode, other.mode), self.boolean | other.boolean)
    }
}

impl<N: Network> BitOrAssign for Boolean<N> {
    /// Sets `self` as the bitwise `OR` of `self` and `other`.
    #[inline]
    fn bitor_assign(&mut self, other: Self) {
        *self = Boolean::new(Mode::combine(self.mode, other.mode), self.boolean | other.boolean)
    }
}

impl<N: Network> BitXor for Boolean<N> {
    type Output = Boolean<N>;

    /// Returns the bitwise `XOR` of `self` and `other`.
    #[inline]
    fn bitxor(self, other: Self) -> Self::Output {
        Boolean::new(Mode::combine(self.mode, other.mode), self.boolean ^ other.boolean)
    }
}

impl<N: Network> BitXorAssign for Boolean<N> {
    /// Sets `self` as the bitwise `XOR` of `self` and `other`.
    #[inline]
    fn bitxor_assign(&mut self, other: Self) {
        *self = Boolean::new(Mode::combine(self.mode, other.mode), self.boolean ^ other.boolean)
    }
}

impl<N: Network> Nand for Boolean<N> {
    type Output = Boolean<N>;

    /// Returns the bitwise `NAND` of `self` and `other`.
    #[inline]
    fn nand(&self, other: &Self) -> Self::Output {
        Boolean::new(Mode::combine(self.mode, other.mode), !(self.boolean & other.boolean))
    }
}

impl<N: Network> Nor for Boolean<N> {
    type Output = Boolean<N>;

    /// Returns the bitwise `NOR` of `self` and `other`.
    #[inline]
    fn nor(&self, other: &Self) -> Self::Output {
        Boolean::new(Mode::combine(self.mode, other.mode), !(self.boolean | other.boolean))
    }
}
