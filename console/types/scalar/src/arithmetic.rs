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

impl<N: Network> Neg for Scalar<N> {
    type Output = Scalar<N>;

    /// Returns the `negation` of `self`.
    #[inline]
    fn neg(self) -> Self::Output {
        Scalar::new(-self.scalar)
    }
}

impl<N: Network> Add<Scalar<N>> for Scalar<N> {
    type Output = Scalar<N>;

    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn add(self, other: Scalar<N>) -> Self::Output {
        Scalar::new(self.scalar + other.scalar)
    }
}

impl<N: Network> AddAssign<Scalar<N>> for Scalar<N> {
    /// Adds `other` to `self`.
    #[inline]
    fn add_assign(&mut self, other: Scalar<N>) {
        self.scalar += other.scalar;
    }
}

impl<N: Network> Sub<Scalar<N>> for Scalar<N> {
    type Output = Scalar<N>;

    /// Returns the `difference` of `self` and `other`.
    #[inline]
    fn sub(self, other: Scalar<N>) -> Self::Output {
        Scalar::new(self.scalar - other.scalar)
    }
}

impl<N: Network> SubAssign<Scalar<N>> for Scalar<N> {
    /// Subtracts `other` from `self`.
    #[inline]
    fn sub_assign(&mut self, other: Scalar<N>) {
        self.scalar -= other.scalar;
    }
}

impl<N: Network> Mul<Scalar<N>> for Scalar<N> {
    type Output = Scalar<N>;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul(self, other: Scalar<N>) -> Self::Output {
        Scalar::new(self.scalar * other.scalar)
    }
}

impl<N: Network> MulAssign<Scalar<N>> for Scalar<N> {
    /// Multiplies `self` by `other`.
    #[inline]
    fn mul_assign(&mut self, other: Scalar<N>) {
        self.scalar *= other.scalar;
    }
}

impl<N: Network> Div<Scalar<N>> for Scalar<N> {
    type Output = Scalar<N>;

    /// Returns the `quotient` of `self` and `other`.
    #[inline]
    fn div(self, other: Scalar<N>) -> Self::Output {
        Scalar::new(self.scalar / other.scalar)
    }
}

impl<N: Network> DivAssign<Scalar<N>> for Scalar<N> {
    /// Divides `self` by `other`.
    #[inline]
    fn div_assign(&mut self, other: Scalar<N>) {
        self.scalar /= other.scalar;
    }
}

impl<N: Network> Pow<Scalar<N>> for Scalar<N> {
    type Output = Scalar<N>;

    /// Returns the `power` of `self` to the power of `other`.
    #[inline]
    fn pow(self, other: Scalar<N>) -> Self::Output {
        Scalar::new(self.scalar.pow(other.scalar.to_repr()))
    }
}

impl<N: Network> Double for Scalar<N> {
    type Output = Scalar<N>;

    /// Returns the `double` of `self`.
    #[inline]
    fn double(&self) -> Self::Output {
        Scalar::new(self.scalar.double())
    }
}

impl<N: Network> Inverse for Scalar<N> {
    type Output = Scalar<N>;

    /// Returns the `inverse` of `self`.
    #[inline]
    fn inverse(&self) -> Result<Self::Output> {
        match self.scalar.inverse() {
            Some(inverse) => Ok(Scalar::new(inverse)),
            None => bail!("Failed to invert a scalar element: {self}"),
        }
    }
}

impl<N: Network> Square for Scalar<N> {
    type Output = Scalar<N>;

    /// Returns the `square` of `self`.
    #[inline]
    fn square(&self) -> Self::Output {
        Scalar::new(self.scalar.square())
    }
}
