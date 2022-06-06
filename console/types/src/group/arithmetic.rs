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

impl<N: Network> Neg for Group<N> {
    type Output = Group<N>;

    /// Returns the `negation` of `self`.
    #[inline]
    fn neg(self) -> Self::Output {
        Group::from_projective(-self.group)
    }
}

impl<N: Network> Add<Group<N>> for Group<N> {
    type Output = Group<N>;

    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn add(self, other: Group<N>) -> Self::Output {
        Group::from_projective(self.group + other.group)
    }
}

impl<N: Network> AddAssign<Group<N>> for Group<N> {
    /// Adds `other` to `self`.
    #[inline]
    fn add_assign(&mut self, other: Group<N>) {
        self.group += other.group;
    }
}

impl<N: Network> Sub<Group<N>> for Group<N> {
    type Output = Group<N>;

    /// Returns the `difference` of `self` and `other`.
    #[inline]
    fn sub(self, other: Group<N>) -> Self::Output {
        Group::from_projective(self.group - other.group)
    }
}

impl<N: Network> SubAssign<Group<N>> for Group<N> {
    /// Subtracts `other` from `self`.
    #[inline]
    fn sub_assign(&mut self, other: Group<N>) {
        self.group -= other.group;
    }
}

impl<N: Network> Mul<Scalar<N>> for Group<N> {
    type Output = Group<N>;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul(self, other: Scalar<N>) -> Self::Output {
        Group::from_projective(self.group * *other)
    }
}

impl<N: Network> MulAssign<Scalar<N>> for Group<N> {
    /// Multiplies `self` by `other`.
    #[inline]
    fn mul_assign(&mut self, other: Scalar<N>) {
        self.group *= *other;
    }
}

impl<N: Network> Double for Group<N> {
    type Output = Group<N>;

    /// Returns the `double` of `self`.
    #[inline]
    fn double(&self) -> Self::Output {
        Group::from_projective(self.group.double())
    }
}
