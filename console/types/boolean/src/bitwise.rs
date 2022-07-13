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

impl<E: Environment> Equal for Boolean<E> {
    type Output = Boolean<E>;

    /// Returns `true` if `self` and `other` are equal.
    fn is_equal(&self, other: &Self) -> Self::Output {
        Boolean::new(self == other)
    }

    /// Returns `true` if `self` and `other` are *not* equal.
    fn is_not_equal(&self, other: &Self) -> Self::Output {
        Boolean::new(self != other)
    }
}

impl<E: Environment> Not for Boolean<E> {
    type Output = Boolean<E>;

    /// Returns the `negation` of `self`.
    #[inline]
    fn not(self) -> Self::Output {
        Boolean::new(!self.boolean)
    }
}

impl<E: Environment> BitAnd<Boolean<E>> for Boolean<E> {
    type Output = Boolean<E>;

    /// Returns the bitwise `AND`` of `self` and `other`.
    #[inline]
    fn bitand(self, other: Self) -> Self::Output {
        Boolean::new(self.boolean & other.boolean)
    }
}

impl<E: Environment> BitAnd<&Boolean<E>> for Boolean<E> {
    type Output = Boolean<E>;

    /// Returns the bitwise `AND` of `self` and `other`.
    #[inline]
    fn bitand(self, other: &Boolean<E>) -> Self::Output {
        Boolean::new(self.boolean & other.boolean)
    }
}

impl<E: Environment> BitAndAssign for Boolean<E> {
    /// Sets `self` as the bitwise `AND` of `self` and `other`.
    #[inline]
    fn bitand_assign(&mut self, other: Self) {
        *self = Boolean::new(self.boolean & other.boolean)
    }
}

impl<E: Environment> BitOr for Boolean<E> {
    type Output = Boolean<E>;

    /// Returns the bitwise `OR` of `self` and `other`.
    #[inline]
    fn bitor(self, other: Self) -> Self::Output {
        Boolean::new(self.boolean | other.boolean)
    }
}

impl<E: Environment> BitOr<&Boolean<E>> for Boolean<E> {
    type Output = Boolean<E>;

    /// Returns the bitwise `OR` of `self` and `other`.
    #[inline]
    fn bitor(self, other: &Boolean<E>) -> Self::Output {
        Boolean::new(self.boolean | other.boolean)
    }
}

impl<E: Environment> BitOrAssign for Boolean<E> {
    /// Sets `self` as the bitwise `OR` of `self` and `other`.
    #[inline]
    fn bitor_assign(&mut self, other: Self) {
        *self = Boolean::new(self.boolean | other.boolean)
    }
}

impl<E: Environment> BitXor for Boolean<E> {
    type Output = Boolean<E>;

    /// Returns the bitwise `XOR` of `self` and `other`.
    #[inline]
    fn bitxor(self, other: Self) -> Self::Output {
        Boolean::new(self.boolean ^ other.boolean)
    }
}

impl<E: Environment> BitXor<&Boolean<E>> for Boolean<E> {
    type Output = Boolean<E>;

    /// Returns the bitwise `XOR` of `self` and `other`.
    #[inline]
    fn bitxor(self, other: &Boolean<E>) -> Self::Output {
        Boolean::new(self.boolean ^ other.boolean)
    }
}

impl<E: Environment> BitXorAssign for Boolean<E> {
    /// Sets `self` as the bitwise `XOR` of `self` and `other`.
    #[inline]
    fn bitxor_assign(&mut self, other: Self) {
        *self = Boolean::new(self.boolean ^ other.boolean)
    }
}

impl<E: Environment> Nand for Boolean<E> {
    type Output = Boolean<E>;

    /// Returns the bitwise `NAND` of `self` and `other`.
    #[inline]
    fn nand(&self, other: &Self) -> Self::Output {
        Boolean::new(!(self.boolean & other.boolean))
    }
}

impl<E: Environment> Nor for Boolean<E> {
    type Output = Boolean<E>;

    /// Returns the bitwise `NOR` of `self` and `other`.
    #[inline]
    fn nor(&self, other: &Self) -> Self::Output {
        Boolean::new(!(self.boolean | other.boolean))
    }
}

impl<E: Environment> Ternary for Boolean<E> {
    type Boolean = Boolean<E>;
    type Output = Self;

    /// Returns `first` if `condition` is `true`, otherwise returns `second`.
    fn ternary(condition: &Self::Boolean, first: &Self, second: &Self) -> Self::Output {
        match **condition {
            true => *first,
            false => *second,
        }
    }
}
