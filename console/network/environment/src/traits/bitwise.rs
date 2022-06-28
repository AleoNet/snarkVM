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

/// Trait for equality comparisons.
pub trait Equal<Rhs: ?Sized = Self> {
    type Output;

    /// Returns `true` if `self` and `other` are equal.
    fn is_equal(&self, other: &Rhs) -> Self::Output;

    /// Returns `true` if `self` and `other` are *not* equal.
    fn is_not_equal(&self, other: &Rhs) -> Self::Output;
}

/// Trait for comparator operations.
pub trait Compare<Rhs: ?Sized = Self> {
    type Output;

    /// Returns `true` if `self` is less than `other`.
    fn is_less_than(&self, other: &Rhs) -> Self::Output;

    /// Returns `true` if `self` is greater than `other`.
    fn is_greater_than(&self, other: &Rhs) -> Self::Output;

    /// Returns `true` if `self` is less than or equal to `other`.
    fn is_less_than_or_equal(&self, other: &Rhs) -> Self::Output;

    /// Returns `true` if `self` is greater than or equal to `other`.
    fn is_greater_than_or_equal(&self, other: &Rhs) -> Self::Output;
}

/// Binary operator for performing `NOT (a AND b)`.
pub trait Nand<Rhs: ?Sized = Self> {
    type Output;

    /// Returns `NOT (a AND b)`.
    fn nand(&self, other: &Rhs) -> Self::Output;
}

/// Binary operator for performing `(NOT a) AND (NOT b)`.
pub trait Nor<Rhs: ?Sized = Self> {
    type Output;

    /// Returns `(NOT a) AND (NOT b)`.
    fn nor(&self, other: &Rhs) -> Self::Output;
}

/// Trait for ternary operations.
pub trait Ternary {
    type Boolean;
    type Output;

    /// Returns `first` if `condition` is `true`, otherwise returns `second`.
    fn ternary(condition: &Self::Boolean, first: &Self, second: &Self) -> Self::Output
    where
        Self: Sized;
}
