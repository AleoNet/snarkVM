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

use crate::{BooleanTrait, Count, Mode};

// /// Trait for uniformly invoking operations.
// pub trait Operation<Op: ?Sized> {
//     type Input;
//     type Output;
//
//     fn invoke(input: Self::Input) -> Self::Output;
// }

// TODO: Remove this trait if it is not used.
/// Trait for metadata on operations.
pub trait MetadataForOp<Op: ?Sized>: CountForOp<Op> + OutputModeForOp<Op> {}

/// Trait for determining the number of constants, public input, private inputs, and constraints for an operation.
pub trait CountForOp<Op: ?Sized> {
    type Case;

    /// Returns the number of constants, public inputs, private inputs, and constraints.
    fn count(input: &Self::Case) -> Count;
}

/// Trait for determining the mode of the output of an operation.
pub trait OutputModeForOp<Op: ?Sized> {
    type Case;

    /// Returns the mode of the output.
    fn output_mode(input: &Self::Case) -> Mode;
}

/// Trait for equality comparisons.
pub trait Equal<Rhs: ?Sized = Self> {
    type Boolean: BooleanTrait;

    /// Returns `true` if `self` and `other` are equal.
    fn is_equal(&self, other: &Rhs) -> Self::Boolean;

    /// Returns `true` if `self` and `other` are *not* equal.
    fn is_not_equal(&self, other: &Rhs) -> Self::Boolean;
}

/// Trait for comparator operations.
pub trait Compare<Rhs: ?Sized = Self> {
    type Boolean: BooleanTrait;

    /// Returns `true` if `self` is less than `other`.
    fn is_less_than(&self, other: &Rhs) -> Self::Boolean;

    /// Returns `true` if `self` is greater than `other`.
    fn is_greater_than(&self, other: &Rhs) -> Self::Boolean;

    /// Returns `true` if `self` is less than or equal to `other`.
    fn is_less_than_or_equal(&self, other: &Rhs) -> Self::Boolean;

    /// Returns `true` if `self` is greater than or equal to `other`.
    fn is_greater_than_or_equal(&self, other: &Rhs) -> Self::Boolean;
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
    type Boolean: BooleanTrait;
    type Output;

    /// Returns `first` if `condition` is `true`, otherwise returns `second`.
    fn ternary(condition: &Self::Boolean, first: &Self, second: &Self) -> Self::Output;
}

/// Binary operator for adding two values, enforcing an overflow never occurs.
pub trait AddChecked<Rhs: ?Sized = Self> {
    type Output;

    fn add_checked(&self, rhs: &Rhs) -> Self::Output;
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

/// Binary operator for dividing two values, enforcing an overflow never occurs.
pub trait DivChecked<Rhs: ?Sized = Self> {
    type Output;

    fn div_checked(&self, rhs: &Rhs) -> Self::Output;
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

/// Binary operator for multiplying two values, enforcing an overflow never occurs.
pub trait MulChecked<Rhs: ?Sized = Self> {
    type Output;

    fn mul_checked(&self, rhs: &Rhs) -> Self::Output;
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

/// Binary operator for exponentiating two values, wrapping the result if an overflow occurs.
pub trait PowWrapped<Rhs: ?Sized = Self> {
    type Output;

    fn pow_wrapped(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for left shifting a value, checking that the rhs is less than the number
/// of bits in self.
pub trait ShlChecked<Rhs: ?Sized = Self> {
    type Output;

    fn shl_checked(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for left shifting a value, checking that the rhs is less than the number
/// of bits in self.
pub trait ShlWrapped<Rhs: ?Sized = Self> {
    type Output;

    fn shl_wrapped(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for right shifting a value, checking that the rhs is less than the number
/// of bits in self.
pub trait ShrChecked<Rhs: ?Sized = Self> {
    type Output;

    fn shr_checked(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for right shifting a value, checking that the rhs is less than the number
/// of bits in self.
pub trait ShrWrapped<Rhs: ?Sized = Self> {
    type Output;

    fn shr_wrapped(&self, rhs: &Rhs) -> Self::Output;
}

/// Binary operator for subtracting two values, enforcing an underflow never occurs.
pub trait SubChecked<Rhs: ?Sized = Self> {
    type Output;

    fn sub_checked(&self, rhs: &Rhs) -> Self::Output;
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

    fn double(self) -> Self::Output;
}

/// Unary operator for retrieving the squared value.
pub trait Square {
    type Output;

    fn square(&self) -> Self::Output;
}

///
/// A single-bit binary adder with a carry bit.
///
/// https://en.wikipedia.org/wiki/Adder_(electronics)#Full_adder
///
/// sum = (a XOR b) XOR carry
/// carry = a AND b OR carry AND (a XOR b)
/// return (sum, carry)
///
pub trait Adder {
    type Carry;
    type Sum;

    /// Returns the sum of `self` and `other` as a sum bit and carry bit.
    fn adder(&self, other: &Self, carry: &Self) -> (Self::Sum, Self::Carry);
}

///
/// A single-bit binary subtractor with a borrow bit.
///
/// https://en.wikipedia.org/wiki/Subtractor#Full_subtractor
///
/// difference = (a XOR b) XOR borrow
/// borrow = ((NOT a) AND b) OR (borrow AND (NOT (a XOR b)))
/// return (difference, borrow)
///
pub trait Subtractor {
    type Borrow;
    type Difference;

    /// Returns the difference of `self` and `other` as a difference bit and borrow bit.
    fn subtractor(&self, other: &Self, borrow: &Self) -> (Self::Difference, Self::Borrow);
}

/// Representation of the zero value.
pub trait Zero {
    type Boolean: BooleanTrait;

    /// Returns a new zero constant.
    fn zero() -> Self;

    /// Returns `true` if `self` is zero.
    fn is_zero(&self) -> Self::Boolean;
}

/// Representation of the one value.
pub trait One {
    type Boolean: BooleanTrait;

    /// Returns a new one constant.
    fn one() -> Self;

    /// Returns `true` if `self` is one.
    fn is_one(&self) -> Self::Boolean;
}

/// Unary operator for retrieving the most-significant bit.
pub trait MSB {
    type Boolean: BooleanTrait;

    /// Returns the MSB of the value.
    fn msb(&self) -> &Self::Boolean;
}
