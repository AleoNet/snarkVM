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

impl<E: Environment> Neg for Scalar<E> {
    type Output = Scalar<E>;

    /// Returns the `negation` of `self`.
    #[inline]
    fn neg(self) -> Self::Output {
        Scalar::new(-self.scalar)
    }
}

impl<E: Environment> Add<Scalar<E>> for Scalar<E> {
    type Output = Scalar<E>;

    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn add(self, other: Scalar<E>) -> Self::Output {
        Scalar::new(self.scalar + other.scalar)
    }
}

impl<E: Environment> Add<&Scalar<E>> for Scalar<E> {
    type Output = Scalar<E>;

    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn add(self, other: &Scalar<E>) -> Self::Output {
        Scalar::new(self.scalar + other.scalar)
    }
}

impl<E: Environment> AddAssign<Scalar<E>> for Scalar<E> {
    /// Adds `other` to `self`.
    #[inline]
    fn add_assign(&mut self, other: Scalar<E>) {
        self.scalar += other.scalar;
    }
}

impl<E: Environment> AddAssign<&Scalar<E>> for Scalar<E> {
    /// Adds `other` to `self`.
    #[inline]
    fn add_assign(&mut self, other: &Scalar<E>) {
        self.scalar += other.scalar;
    }
}

impl<E: Environment> Sub<Scalar<E>> for Scalar<E> {
    type Output = Scalar<E>;

    /// Returns the `difference` of `self` and `other`.
    #[inline]
    fn sub(self, other: Scalar<E>) -> Self::Output {
        Scalar::new(self.scalar - other.scalar)
    }
}

impl<E: Environment> Sub<&Scalar<E>> for Scalar<E> {
    type Output = Scalar<E>;

    /// Returns the `difference` of `self` and `other`.
    #[inline]
    fn sub(self, other: &Scalar<E>) -> Self::Output {
        Scalar::new(self.scalar - other.scalar)
    }
}

impl<E: Environment> SubAssign<Scalar<E>> for Scalar<E> {
    /// Subtracts `other` from `self`.
    #[inline]
    fn sub_assign(&mut self, other: Scalar<E>) {
        self.scalar -= other.scalar;
    }
}

impl<E: Environment> SubAssign<&Scalar<E>> for Scalar<E> {
    /// Subtracts `other` from `self`.
    #[inline]
    fn sub_assign(&mut self, other: &Scalar<E>) {
        self.scalar -= other.scalar;
    }
}

impl<E: Environment> Mul<Scalar<E>> for Scalar<E> {
    type Output = Scalar<E>;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul(self, other: Scalar<E>) -> Self::Output {
        Scalar::new(self.scalar * other.scalar)
    }
}

impl<E: Environment> Mul<&Scalar<E>> for Scalar<E> {
    type Output = Scalar<E>;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul(self, other: &Scalar<E>) -> Self::Output {
        Scalar::new(self.scalar * other.scalar)
    }
}

impl<E: Environment> MulAssign<Scalar<E>> for Scalar<E> {
    /// Multiplies `self` by `other`.
    #[inline]
    fn mul_assign(&mut self, other: Scalar<E>) {
        self.scalar *= other.scalar;
    }
}

impl<E: Environment> MulAssign<&Scalar<E>> for Scalar<E> {
    /// Multiplies `self` by `other`.
    #[inline]
    fn mul_assign(&mut self, other: &Scalar<E>) {
        self.scalar *= other.scalar;
    }
}

impl<E: Environment> Div<Scalar<E>> for Scalar<E> {
    type Output = Scalar<E>;

    /// Returns the `quotient` of `self` and `other`.
    #[inline]
    fn div(self, other: Scalar<E>) -> Self::Output {
        Scalar::new(self.scalar / other.scalar)
    }
}

impl<E: Environment> Div<&Scalar<E>> for Scalar<E> {
    type Output = Scalar<E>;

    /// Returns the `quotient` of `self` and `other`.
    #[inline]
    fn div(self, other: &Scalar<E>) -> Self::Output {
        Scalar::new(self.scalar / other.scalar)
    }
}

impl<E: Environment> DivAssign<Scalar<E>> for Scalar<E> {
    /// Divides `self` by `other`.
    #[inline]
    fn div_assign(&mut self, other: Scalar<E>) {
        self.scalar /= other.scalar;
    }
}

impl<E: Environment> DivAssign<&Scalar<E>> for Scalar<E> {
    /// Divides `self` by `other`.
    #[inline]
    fn div_assign(&mut self, other: &Scalar<E>) {
        self.scalar /= other.scalar;
    }
}

impl<E: Environment> Pow<Scalar<E>> for Scalar<E> {
    type Output = Scalar<E>;

    /// Returns the `power` of `self` to the power of `other`.
    #[inline]
    fn pow(self, other: Scalar<E>) -> Self::Output {
        Scalar::new(self.scalar.pow(other.scalar.to_repr()))
    }
}

impl<E: Environment> Pow<&Scalar<E>> for Scalar<E> {
    type Output = Scalar<E>;

    /// Returns the `power` of `self` to the power of `other`.
    #[inline]
    fn pow(self, other: &Scalar<E>) -> Self::Output {
        Scalar::new(self.scalar.pow(other.scalar.to_repr()))
    }
}

impl<E: Environment> Double for Scalar<E> {
    type Output = Scalar<E>;

    /// Returns the `double` of `self`.
    #[inline]
    fn double(&self) -> Self::Output {
        Scalar::new(self.scalar.double())
    }
}

impl<E: Environment> Inverse for Scalar<E> {
    type Output = Scalar<E>;

    /// Returns the `inverse` of `self`.
    #[inline]
    fn inverse(&self) -> Result<Self::Output> {
        match self.scalar.inverse() {
            Some(inverse) => Ok(Scalar::new(inverse)),
            None => bail!("Failed to invert a scalar element: {self}"),
        }
    }
}

impl<E: Environment> Square for Scalar<E> {
    type Output = Scalar<E>;

    /// Returns the `square` of `self`.
    #[inline]
    fn square(&self) -> Self::Output {
        Scalar::new(self.scalar.square())
    }
}

impl<E: Environment> Sum<Scalar<E>> for Scalar<E> {
    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn sum<I: Iterator<Item = Scalar<E>>>(iter: I) -> Self {
        iter.fold(Scalar::zero(), |a, b| a + b)
    }
}

impl<'a, E: Environment> Sum<&'a Scalar<E>> for Scalar<E> {
    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn sum<I: Iterator<Item = &'a Scalar<E>>>(iter: I) -> Self {
        iter.fold(Scalar::zero(), |a, b| a + b)
    }
}

impl<E: Environment> Product<Scalar<E>> for Scalar<E> {
    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn product<I: Iterator<Item = Scalar<E>>>(iter: I) -> Self {
        iter.fold(Scalar::one(), |a, b| a * b)
    }
}

impl<'a, E: Environment> Product<&'a Scalar<E>> for Scalar<E> {
    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn product<I: Iterator<Item = &'a Scalar<E>>>(iter: I) -> Self {
        iter.fold(Scalar::one(), |a, b| a * b)
    }
}
