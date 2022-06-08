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

impl<N: Network> Neg for Field<N> {
    type Output = Field<N>;

    /// Returns the `negation` of `self`.
    #[inline]
    fn neg(self) -> Self::Output {
        Field::new(-self.field)
    }
}

impl<N: Network> Add<Field<N>> for Field<N> {
    type Output = Field<N>;

    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn add(self, other: Field<N>) -> Self::Output {
        Field::new(self.field + other.field)
    }
}

impl<N: Network> AddAssign<Field<N>> for Field<N> {
    /// Adds `other` to `self`.
    #[inline]
    fn add_assign(&mut self, other: Field<N>) {
        self.field += other.field;
    }
}

impl<N: Network> Sub<Field<N>> for Field<N> {
    type Output = Field<N>;

    /// Returns the `difference` of `self` and `other`.
    #[inline]
    fn sub(self, other: Field<N>) -> Self::Output {
        Field::new(self.field - other.field)
    }
}

impl<N: Network> SubAssign<Field<N>> for Field<N> {
    /// Subtracts `other` from `self`.
    #[inline]
    fn sub_assign(&mut self, other: Field<N>) {
        self.field -= other.field;
    }
}

impl<N: Network> Mul<Field<N>> for Field<N> {
    type Output = Field<N>;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul(self, other: Field<N>) -> Self::Output {
        Field::new(self.field * other.field)
    }
}

impl<N: Network> MulAssign<Field<N>> for Field<N> {
    /// Multiplies `self` by `other`.
    #[inline]
    fn mul_assign(&mut self, other: Field<N>) {
        self.field *= other.field;
    }
}

impl<N: Network> Div<Field<N>> for Field<N> {
    type Output = Field<N>;

    /// Returns the `quotient` of `self` and `other`.
    #[inline]
    fn div(self, other: Field<N>) -> Self::Output {
        Field::new(self.field / other.field)
    }
}

impl<N: Network> DivAssign<Field<N>> for Field<N> {
    /// Divides `self` by `other`.
    #[inline]
    fn div_assign(&mut self, other: Field<N>) {
        self.field /= other.field;
    }
}

impl<N: Network> Pow<Field<N>> for Field<N> {
    type Output = Field<N>;

    /// Returns the `power` of `self` to the power of `other`.
    #[inline]
    fn pow(self, other: Field<N>) -> Self::Output {
        Field::new(self.field.pow(other.field.to_repr()))
    }
}

impl<N: Network> Double for Field<N> {
    type Output = Field<N>;

    /// Returns the `double` of `self`.
    #[inline]
    fn double(&self) -> Self::Output {
        Field::new(self.field.double())
    }
}

impl<N: Network> Inverse for Field<N> {
    type Output = Field<N>;

    /// Returns the `inverse` of `self`.
    #[inline]
    fn inverse(&self) -> Result<Self::Output> {
        match self.field.inverse() {
            Some(inverse) => Ok(Field::new(inverse)),
            None => bail!("Failed to invert a field element: {self}"),
        }
    }
}

impl<N: Network> Square for Field<N> {
    type Output = Field<N>;

    /// Returns the `square` of `self`.
    #[inline]
    fn square(&self) -> Self::Output {
        Field::new(self.field.square())
    }
}

impl<N: Network> SquareRoot for Field<N> {
    type Output = Field<N>;

    /// Returns the `square_root` of `self`.
    #[inline]
    fn square_root(&self) -> Result<Self::Output> {
        match self.field.sqrt() {
            Some(sqrt) => Ok(Field::new(sqrt)),
            None => bail!("Failed to square root a field element: {self}"),
        }
    }
}
