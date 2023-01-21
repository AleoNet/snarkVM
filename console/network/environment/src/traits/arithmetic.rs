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

use anyhow::Result;

/// Binary operator for adding two values, enforcing an overflow never occurs.
pub trait AddChecked<Rhs: ?Sized = Self> {
    type Output;

    fn add_checked(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for adding two values, indicating whether or not an overflow occurs via a flag.
pub trait AddFlagged<Rhs: ?Sized = Self> {
    type Output;

    fn add_flagged(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for adding two values, bounding the sum to `MAX` if an overflow occurs.
pub trait AddSaturating<Rhs: ?Sized = Self> {
    type Output;

    fn add_saturating(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for adding two values, wrapping the sum if an overflow occurs.
pub trait AddWrapped<Rhs: ?Sized = Self> {
    type Output;

    fn add_wrapped(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for dividing two values, without checking specific conditions.
pub trait DivUnchecked<Rhs: ?Sized = Self> {
    type Output;

    fn div_unchecked(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for dividing two values, enforcing an overflow never occurs.
pub trait DivChecked<Rhs: ?Sized = Self> {
    type Output;

    fn div_checked(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for dividing two values, indicating whether or not an overflow or division by zero error occurs via a flag.
pub trait DivFlagged<Rhs: ?Sized = Self> {
    type Output;

    fn div_flagged(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for dividing two values, bounding the quotient to `MAX` or `MIN` if an overflow occurs.
pub trait DivSaturating<Rhs: ?Sized = Self> {
    type Output;

    fn div_saturating(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for dividing two values, wrapping the quotient if an overflow occurs.
pub trait DivWrapped<Rhs: ?Sized = Self> {
    type Output;

    fn div_wrapped(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for modding two values.
pub trait Modulo<Rhs: ?Sized = Self> {
    type Output;

    fn modulo(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for modding two values, indicating whether or not a division by zero error occurs via a flag.
pub trait ModuloFlagged<Rhs: ?Sized = Self> {
    type Output;

    fn modulo_flagged(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for multiplying two values, enforcing an overflow never occurs.
pub trait MulChecked<Rhs: ?Sized = Self> {
    type Output;

    fn mul_checked(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for multiplying two values, indicating whether or not an overflow occurs via a flag.
pub trait MulFlagged<Rhs: ?Sized = Self> {
    type Output;

    fn mul_flagged(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for multiplying two values, bounding the product to `MAX` if an overflow occurs.
pub trait MulSaturating<Rhs: ?Sized = Self> {
    type Output;

    fn mul_saturating(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for multiplying two values, wrapping the product if an overflow occurs.
pub trait MulWrapped<Rhs: ?Sized = Self> {
    type Output;

    fn mul_wrapped(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for exponentiating two values, enforcing an overflow never occurs.
pub trait PowChecked<Rhs: ?Sized = Self> {
    type Output;

    fn pow_checked(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for exponentiating two values, indicating whether or not an overflow occurs via a flag.
pub trait PowFlagged<Rhs: ?Sized = Self> {
    type Output;

    fn pow_flagged(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for exponentiating two values, wrapping the result if an overflow occurs.
pub trait PowWrapped<Rhs: ?Sized = Self> {
    type Output;

    fn pow_wrapped(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for dividing two values and returning the remainder, enforcing an overflow never occurs.
pub trait RemChecked<Rhs: ?Sized = Self> {
    type Output;

    fn rem_checked(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for dividing two values and return the remainder, indicating whether or not an overflow occurs via flag.
pub trait RemFlagged<Rhs: ?Sized = Self> {
    type Output;

    fn rem_flagged(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for dividing two values, bounding the remainder to `MAX` or `MIN` if an overflow occurs.
pub trait RemSaturating<Rhs: ?Sized = Self> {
    type Output;

    fn rem_saturating(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for dividing two values, wrapping the remainder if an overflow occurs.
pub trait RemWrapped<Rhs: ?Sized = Self> {
    type Output;

    fn rem_wrapped(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for left shifting a value, checking that the rhs is less than the number of bits in self.
pub trait ShlChecked<Rhs: ?Sized = Self> {
    type Output;

    fn shl_checked(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for left shifting a values, indicating that the rhs is less than the number of bits in self via flag.
pub trait ShlFlagged<Rhs: ?Sized = Self> {
    type Output;

    fn shl_flagged(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for left shifting a value, safely continuing past the number of bits in self.
pub trait ShlWrapped<Rhs: ?Sized = Self> {
    type Output;

    fn shl_wrapped(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for right shifting a value, checking that the rhs is less than the number of bits in self.
pub trait ShrChecked<Rhs: ?Sized = Self> {
    type Output;

    fn shr_checked(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for right shifting a value, indicating that the rhs is less than the number of bits in self via a flag.
pub trait ShrFlagged<Rhs: ?Sized = Self> {
    type Output;

    fn shr_flagged(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for right shifting a value, safely continuing past the number of bits in self.
pub trait ShrWrapped<Rhs: ?Sized = Self> {
    type Output;

    fn shr_wrapped(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for subtracting two values, enforcing an underflow never occurs.
pub trait SubChecked<Rhs: ?Sized = Self> {
    type Output;

    fn sub_checked(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for subtracting two values, indicating whether or not an overflow occurs via a flag.
pub trait SubFlagged<Rhs: ?Sized = Self> {
    type Output;

    fn sub_flagged(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for subtracting two values, bounding the difference to `MIN` if an underflow occurs.
pub trait SubSaturating<Rhs: ?Sized = Self> {
    type Output;

    fn sub_saturating(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for subtracting two values, wrapping the difference if an underflow occurs.
pub trait SubWrapped<Rhs: ?Sized = Self> {
    type Output;

    fn sub_wrapped(&self, rhs: &Rhs) -> Self::Output;
}

/// Unary operator for retrieving the absolute value, enforcing an overflow never occurs.
pub trait AbsChecked {
    type Output;

    fn abs_checked(self) -> Self::Output;
}

/// Unary operator for retreiving the absolute value, indicating whether or not an overflow occurs via a flag.
pub trait AbsFlagged {
    type Output;

    fn abs_flagged(self) -> Self::Output;
}

/// Unary operator for retrieving the absolute value, bounding the difference to `MAX` if an overflow occurs.
pub trait AbsSaturating {
    type Output;

    fn abs_saturating(self) -> Self::Output;
}

/// Unary operator for retrieving the absolute value, wrapping the result if an overflow occurs.
pub trait AbsWrapped {
    type Output;

    fn abs_wrapped(self) -> Self::Output;
}

/// Unary operator for retrieving the doubled value.
pub trait Double {
    type Output;

    fn double(&self) -> Self::Output;
}

/// Unary operator for retrieving the inverse value.
pub trait Inverse {
    type Output;

    fn inverse(&self) -> Result<Self::Output>;
}

/// Unary operator for retrieving the inverse value, indicating whether or not an overflow occurs via a flag.
pub trait InverseFlagged {
    type Output;

    fn inverse_flagged(&self) -> Self::Output;
}

/// Unary operator for retrieving the negated value, indicating whether or not an overflow occurs via a flag.
pub trait NegFlagged {
    type Output;

    fn neg_flagged(self) -> Self::Output;
}

/// Unary operator for retrieving the squared value.
pub trait Square {
    type Output;

    fn square(&self) -> Self::Output;
}

/// Unary operator for retrieving the squared value, indicating whether or not an overflow occurs via a flag.
pub trait SquareFlagged {
    type Output;

    fn square_flagged(&self) -> Self::Output;
}

/// Unary operator for retrieving the square root of the value.
pub trait SquareRoot {
    type Output;

    fn square_root(&self) -> Result<Self::Output>;
}

/// Unary operator for retrieving the square root of the value, indicating whether or not an overflow occurs via a flag.
pub trait SquareRootFlagged {
    type Output;

    fn square_root_flagged(&self) -> Self::Output;
}
