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

impl<E: Environment> Neg for Group<E> {
    type Output = Group<E>;

    /// Returns the `negation` of `self`.
    #[inline]
    fn neg(self) -> Self::Output {
        Group::from_projective(-self.group)
    }
}

impl<E: Environment> Add<Group<E>> for Group<E> {
    type Output = Group<E>;

    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn add(self, other: Group<E>) -> Self::Output {
        Group::from_projective(self.group + other.group)
    }
}

impl<E: Environment> Add<&Group<E>> for Group<E> {
    type Output = Group<E>;

    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn add(self, other: &Group<E>) -> Self::Output {
        Group::from_projective(self.group + other.group)
    }
}

impl<E: Environment> AddAssign<Group<E>> for Group<E> {
    /// Adds `other` to `self`.
    #[inline]
    fn add_assign(&mut self, other: Group<E>) {
        self.group += other.group;
    }
}

impl<E: Environment> AddAssign<&Group<E>> for Group<E> {
    /// Adds `other` to `self`.
    #[inline]
    fn add_assign(&mut self, other: &Group<E>) {
        self.group += other.group;
    }
}

impl<E: Environment> Sub<Group<E>> for Group<E> {
    type Output = Group<E>;

    /// Returns the `difference` of `self` and `other`.
    #[inline]
    fn sub(self, other: Group<E>) -> Self::Output {
        Group::from_projective(self.group - other.group)
    }
}

impl<E: Environment> Sub<&Group<E>> for Group<E> {
    type Output = Group<E>;

    /// Returns the `difference` of `self` and `other`.
    #[inline]
    fn sub(self, other: &Group<E>) -> Self::Output {
        Group::from_projective(self.group - other.group)
    }
}

impl<E: Environment> SubAssign<Group<E>> for Group<E> {
    /// Subtracts `other` from `self`.
    #[inline]
    fn sub_assign(&mut self, other: Group<E>) {
        self.group -= other.group;
    }
}

impl<E: Environment> SubAssign<&Group<E>> for Group<E> {
    /// Subtracts `other` from `self`.
    #[inline]
    fn sub_assign(&mut self, other: &Group<E>) {
        self.group -= other.group;
    }
}

impl<E: Environment> Mul<Scalar<E>> for Group<E> {
    type Output = Group<E>;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul(self, other: Scalar<E>) -> Self::Output {
        Group::from_projective(self.group * *other)
    }
}

impl<E: Environment> Mul<&Scalar<E>> for Group<E> {
    type Output = Group<E>;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul(self, other: &Scalar<E>) -> Self::Output {
        Group::from_projective(self.group * **other)
    }
}

impl<E: Environment> Mul<Group<E>> for Scalar<E> {
    type Output = Group<E>;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul(self, other: Group<E>) -> Self::Output {
        Group::from_projective(other.group * *self)
    }
}

impl<E: Environment> Mul<&Group<E>> for Scalar<E> {
    type Output = Group<E>;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul(self, other: &Group<E>) -> Self::Output {
        Group::from_projective(other.group * *self)
    }
}

impl<E: Environment> MulAssign<Scalar<E>> for Group<E> {
    /// Multiplies `self` by `other`.
    #[inline]
    fn mul_assign(&mut self, other: Scalar<E>) {
        self.group *= *other;
    }
}

impl<E: Environment> MulAssign<&Scalar<E>> for Group<E> {
    /// Multiplies `self` by `other`.
    #[inline]
    fn mul_assign(&mut self, other: &Scalar<E>) {
        self.group *= **other;
    }
}

impl<E: Environment> Double for Group<E> {
    type Output = Group<E>;

    /// Returns the `double` of `self`.
    #[inline]
    fn double(&self) -> Self::Output {
        Group::from_projective(self.group.double())
    }
}

impl<E: Environment> Sum<Group<E>> for Group<E> {
    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn sum<I: Iterator<Item = Group<E>>>(iter: I) -> Self {
        iter.fold(Group::zero(), |a, b| a + b)
    }
}

impl<'a, E: Environment> Sum<&'a Group<E>> for Group<E> {
    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn sum<I: Iterator<Item = &'a Group<E>>>(iter: I) -> Self {
        iter.fold(Group::zero(), |a, b| a + b)
    }
}
