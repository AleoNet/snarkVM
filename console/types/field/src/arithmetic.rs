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

impl<E: Environment> Neg for Field<E> {
    type Output = Field<E>;

    /// Returns the `negation` of `self`.
    #[inline]
    fn neg(self) -> Self::Output {
        Field::new(-self.field)
    }
}

impl<E: Environment> Add<Field<E>> for Field<E> {
    type Output = Field<E>;

    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn add(self, other: Field<E>) -> Self::Output {
        Field::new(self.field + other.field)
    }
}

impl<E: Environment> Add<&Field<E>> for Field<E> {
    type Output = Field<E>;

    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn add(self, other: &Field<E>) -> Self::Output {
        Field::new(self.field + other.field)
    }
}

impl<E: Environment> AddAssign<Field<E>> for Field<E> {
    /// Adds `other` to `self`.
    #[inline]
    fn add_assign(&mut self, other: Field<E>) {
        self.field += other.field;
    }
}

impl<E: Environment> AddAssign<&Field<E>> for Field<E> {
    /// Adds `other` to `self`.
    #[inline]
    fn add_assign(&mut self, other: &Field<E>) {
        self.field += other.field;
    }
}

impl<E: Environment> Sub<Field<E>> for Field<E> {
    type Output = Field<E>;

    /// Returns the `difference` of `self` and `other`.
    #[inline]
    fn sub(self, other: Field<E>) -> Self::Output {
        Field::new(self.field - other.field)
    }
}

impl<E: Environment> Sub<&Field<E>> for Field<E> {
    type Output = Field<E>;

    /// Returns the `difference` of `self` and `other`.
    #[inline]
    fn sub(self, other: &Field<E>) -> Self::Output {
        Field::new(self.field - other.field)
    }
}

impl<E: Environment> SubAssign<Field<E>> for Field<E> {
    /// Subtracts `other` from `self`.
    #[inline]
    fn sub_assign(&mut self, other: Field<E>) {
        self.field -= other.field;
    }
}

impl<E: Environment> SubAssign<&Field<E>> for Field<E> {
    /// Subtracts `other` from `self`.
    #[inline]
    fn sub_assign(&mut self, other: &Field<E>) {
        self.field -= other.field;
    }
}

impl<E: Environment> Mul<Field<E>> for Field<E> {
    type Output = Field<E>;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul(self, other: Field<E>) -> Self::Output {
        Field::new(self.field * other.field)
    }
}

impl<E: Environment> Mul<&Field<E>> for Field<E> {
    type Output = Field<E>;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul(self, other: &Field<E>) -> Self::Output {
        Field::new(self.field * other.field)
    }
}

impl<E: Environment> MulAssign<Field<E>> for Field<E> {
    /// Multiplies `self` by `other`.
    #[inline]
    fn mul_assign(&mut self, other: Field<E>) {
        self.field *= other.field;
    }
}

impl<E: Environment> MulAssign<&Field<E>> for Field<E> {
    /// Multiplies `self` by `other`.
    #[inline]
    fn mul_assign(&mut self, other: &Field<E>) {
        self.field *= other.field;
    }
}

impl<E: Environment> Div<Field<E>> for Field<E> {
    type Output = Field<E>;

    /// Returns the `quotient` of `self` and `other`.
    #[inline]
    fn div(self, other: Field<E>) -> Self::Output {
        Field::new(self.field / other.field)
    }
}

impl<E: Environment> Div<&Field<E>> for Field<E> {
    type Output = Field<E>;

    /// Returns the `quotient` of `self` and `other`.
    #[inline]
    fn div(self, other: &Field<E>) -> Self::Output {
        Field::new(self.field / other.field)
    }
}

impl<E: Environment> DivAssign<Field<E>> for Field<E> {
    /// Divides `self` by `other`.
    #[inline]
    fn div_assign(&mut self, other: Field<E>) {
        self.field /= other.field;
    }
}

impl<E: Environment> DivAssign<&Field<E>> for Field<E> {
    /// Divides `self` by `other`.
    #[inline]
    fn div_assign(&mut self, other: &Field<E>) {
        self.field /= other.field;
    }
}

impl<E: Environment> Pow<Field<E>> for Field<E> {
    type Output = Field<E>;

    /// Returns the `power` of `self` to the power of `other`.
    #[inline]
    fn pow(self, other: Field<E>) -> Self::Output {
        Field::new(self.field.pow(other.field.to_repr()))
    }
}

impl<E: Environment> Pow<&Field<E>> for Field<E> {
    type Output = Field<E>;

    /// Returns the `power` of `self` to the power of `other`.
    #[inline]
    fn pow(self, other: &Field<E>) -> Self::Output {
        Field::new(self.field.pow(other.field.to_repr()))
    }
}

impl<E: Environment> Double for Field<E> {
    type Output = Field<E>;

    /// Returns the `double` of `self`.
    #[inline]
    fn double(&self) -> Self::Output {
        Field::new(self.field.double())
    }
}

impl<E: Environment> Inverse for Field<E> {
    type Output = Field<E>;

    /// Returns the `inverse` of `self`.
    #[inline]
    fn inverse(&self) -> Result<Self::Output> {
        match self.field.inverse() {
            Some(inverse) => Ok(Field::new(inverse)),
            None => bail!("Failed to invert a field element: {self}"),
        }
    }
}

impl<E: Environment> Square for Field<E> {
    type Output = Field<E>;

    /// Returns the `square` of `self`.
    #[inline]
    fn square(&self) -> Self::Output {
        Field::new(self.field.square())
    }
}

impl<E: Environment> SquareRoot for Field<E> {
    type Output = Field<E>;

    /// Returns the `square_root` of `self`.
    #[inline]
    fn square_root(&self) -> Result<Self::Output> {
        match self.field.sqrt() {
            Some(sqrt) => Ok(Field::new(sqrt)),
            None => bail!("Failed to square root a field element: {self}"),
        }
    }
}

impl<E: Environment> Sum<Field<E>> for Field<E> {
    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn sum<I: Iterator<Item = Field<E>>>(iter: I) -> Self {
        iter.fold(Field::zero(), |a, b| a + b)
    }
}

impl<'a, E: Environment> Sum<&'a Field<E>> for Field<E> {
    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn sum<I: Iterator<Item = &'a Field<E>>>(iter: I) -> Self {
        iter.fold(Field::zero(), |a, b| a + b)
    }
}

impl<E: Environment> Product<Field<E>> for Field<E> {
    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn product<I: Iterator<Item = Field<E>>>(iter: I) -> Self {
        iter.fold(Field::one(), |a, b| a * b)
    }
}

impl<'a, E: Environment> Product<&'a Field<E>> for Field<E> {
    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn product<I: Iterator<Item = &'a Field<E>>>(iter: I) -> Self {
        iter.fold(Field::one(), |a, b| a * b)
    }
}
