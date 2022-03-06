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

use crate::{helpers::integers::IntegerType, Environment, Mode, U16, U32, U8};

use core::{
    fmt::{Debug, Display},
    ops::{
        Add,
        AddAssign,
        BitAnd,
        BitAndAssign,
        BitOr,
        BitOrAssign,
        BitXor,
        BitXorAssign,
        Div,
        DivAssign,
        Mul,
        MulAssign,
        Neg,
        Not,
        Shl,
        ShlAssign,
        Shr,
        ShrAssign,
        Sub,
        SubAssign,
    },
};
use num_traits::Inv;

pub use crate::{Parser, ParserResult};

/// Representation of a boolean.
pub trait BooleanTrait:
    Adder
    + Annotation
    + BitAndAssign
    + BitAnd<Output = Self>
    + BitOrAssign
    + BitOr<Output = Self>
    + BitXorAssign
    + BitXor<Output = Self>
    + Clone
    + Debug
    + Eject<Primitive = bool>
    + Equal
    + Inject<Primitive = bool>
    + Nand
    + Nor
    + Not
    + Parser
    + Subtractor
    + Ternary
{
}

/// Representation of a base field.
pub trait BaseFieldTrait:
    Add<Output = Self>
    + AddAssign
    + Annotation
    + Clone
    + Debug
    + Div<Output = Self>
    + DivAssign
    + Double<Output = Self>
    + Eject
    + Equal
    + FromBits
    + Inject
    + Inv
    + Mul<Output = Self>
    + MulAssign
    + Neg<Output = Self>
    + One
    + Parser
    + Square<Output = Self>
    + Sub<Output = Self>
    + SubAssign
    + Ternary
    + ToBits
    + Zero
{
}

/// Representation of a scalar field.
pub trait ScalarTrait:
    Annotation + Clone + Debug + Eject + Equal + Inject + One + Parser + Ternary + ToBits + Zero
{
}

/// Representation of an integer.
pub trait IntegerTrait<E: Environment, I: IntegerType>:
    AddAssign
    + Add<Output = Self>
    + AddChecked<Output = Self>
    + AddWrapped<Output = Self>
    + Annotation
    + BitAndAssign
    + BitAnd<Output = Self>
    + BitOrAssign
    + BitOr<Output = Self>
    + BitXorAssign
    + BitXor<Output = Self>
    + Clone
    + Debug
    + DivAssign
    + Div<Output = Self>
    + DivChecked<Output = Self>
    + DivWrapped<Output = Self>
    + Eject<Primitive = I>
    + Equal
    + FromBits
    + Inject<Primitive = I>
    + MulAssign
    + Mul<Output = Self>
    + MulChecked<Output = Self>
    + MulWrapped<Output = Self>
    + Neg<Output = Self>
    + Not<Output = Self>
    + One
    + PowChecked<U8<E>, Output = Self>
    + PowChecked<U16<E>, Output = Self>
    + PowChecked<U32<E>, Output = Self>
    + PowWrapped<U8<E>, Output = Self>
    + PowWrapped<U16<E>, Output = Self>
    + PowWrapped<U32<E>, Output = Self>
    + Shl<U8<E>, Output = Self>
    + Shl<U16<E>, Output = Self>
    + Shl<U32<E>, Output = Self>
    + ShlAssign<U8<E>>
    + ShlAssign<U16<E>>
    + ShlAssign<U32<E>>
    + ShlChecked<U8<E>, Output = Self>
    + ShlChecked<U16<E>, Output = Self>
    + ShlChecked<U32<E>, Output = Self>
    + ShlWrapped<U8<E>, Output = Self>
    + ShlWrapped<U16<E>, Output = Self>
    + ShlWrapped<U32<E>, Output = Self>
    + Shr<U8<E>, Output = Self>
    + Shr<U16<E>, Output = Self>
    + Shr<U32<E>, Output = Self>
    + ShrAssign<U8<E>>
    + ShrAssign<U16<E>>
    + ShrAssign<U32<E>>
    + ShrChecked<U8<E>, Output = Self>
    + ShrChecked<U16<E>, Output = Self>
    + ShrChecked<U32<E>, Output = Self>
    + ShrWrapped<U8<E>, Output = Self>
    + ShrWrapped<U16<E>, Output = Self>
    + ShrWrapped<U32<E>, Output = Self>
    + SubAssign
    + Sub<Output = Self>
    + SubChecked<Output = Self>
    + SubWrapped<Output = Self>
    + Ternary
    + ToBits
    + Zero
{
}

/// Operations to inject from a primitive form into a circuit environment.
pub trait Inject {
    type Primitive: Debug + Default;

    ///
    /// Initializes a circuit of the given mode and primitive value.
    ///
    fn new(mode: Mode, value: Self::Primitive) -> Self;

    ///
    /// Initializes a blank default of the circuit for the given mode.
    /// This operation is used commonly to derive a proving and verifying key.
    ///
    fn blank(mode: Mode) -> Self
    where
        Self: Sized,
    {
        Self::new(mode, Default::default())
    }
}

/// Operations to eject from a circuit environment into primitive form.
pub trait Eject {
    type Primitive: Debug + Display;

    ///
    /// Ejects the mode of the circuit type.
    ///
    fn eject_mode(&self) -> Mode;

    ///
    /// Ejects the circuit type as a primitive type value.
    ///
    fn eject_value(&self) -> Self::Primitive;

    ///
    /// Returns `true` if the circuit is a constant.
    ///
    fn is_constant(&self) -> bool {
        self.eject_mode().is_constant()
    }

    ///
    /// Returns `true` if the circuit is a public.
    ///
    fn is_public(&self) -> bool {
        self.eject_mode().is_public()
    }

    ///
    /// Returns `true` if the circuit is a private.
    ///
    fn is_private(&self) -> bool {
        self.eject_mode().is_private()
    }
}

/// Operations to retrieve the type annotation.
pub trait Annotation {
    ///
    /// Returns the type name of the circuit as a string slice. (i.e. "u8")
    ///
    fn type_name() -> &'static str;
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

/// Trait for equality comparisons.
pub trait Equal<Rhs: ?Sized = Self> {
    type Boolean: BooleanTrait;

    /// Returns `true` if `self` and `other` are equal.
    fn is_eq(&self, other: &Rhs) -> Self::Boolean;

    /// Returns `true` if `self` and `other` are *not* equal.
    fn is_neq(&self, other: &Rhs) -> Self::Boolean;
}

pub trait LessThan<Rhs: ?Sized = Self> {
    type Boolean: BooleanTrait;

    /// Returns `true` if `self` is less than `other`.
    fn is_lt(&self, other: &Rhs) -> Self::Boolean;
}

/// Binary operator for performing `NOT (a AND b)`.
pub trait Nand<Rhs: ?Sized = Self> {
    type Boolean: BooleanTrait;
    type Output;

    /// Returns `NOT (a AND b)`.
    fn nand(&self, other: &Rhs) -> Self::Output;
}

/// Binary operator for performing `(NOT a) AND (NOT b)`.
pub trait Nor<Rhs: ?Sized = Self> {
    type Boolean: BooleanTrait;
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

/// Unary operator for retrieving the most-significant bit.
pub trait MSB {
    type Boolean: BooleanTrait;

    /// Returns the MSB of the value.
    fn msb(&self) -> &Self::Boolean;
}

/// Unary operator for instantiating from bits.
pub trait FromBits {
    type Boolean: BooleanTrait;

    fn from_bits_le(mode: Mode, bits_le: &[Self::Boolean]) -> Self;

    fn from_bits_be(mode: Mode, bits_be: &[Self::Boolean]) -> Self;
}

/// Unary operator for converting to bits.
pub trait ToBits {
    type Boolean: BooleanTrait;

    fn to_bits_le(&self) -> Vec<Self::Boolean>;

    fn to_bits_be(&self) -> Vec<Self::Boolean>;
}

/// Unary operator for converting to `k` number of bits.
pub trait ToLowerBits {
    type Boolean: BooleanTrait;

    ///
    /// Outputs the lower `k` bits of an `n`-bit element in little-endian representation.
    /// Enforces that the upper `n - k` bits are zero.
    ///
    fn to_lower_bits_le(&self, k: usize) -> Vec<Self::Boolean>;

    ///
    /// Outputs the lower `k` bits of an `n`-bit element in big-endian representation.
    /// Enforces that the upper `n - k` bits are zero.
    ///
    fn to_lower_bits_be(&self, k: usize) -> Vec<Self::Boolean>;
}

/// Unary operator for converting to `k` number of bits.
pub trait ToUpperBits {
    type Boolean: BooleanTrait;

    ///
    /// Outputs the upper `k` bits of an `n`-bit element in little-endian representation.
    /// Enforces that the lower `n - k` bits are zero.
    ///
    fn to_upper_bits_le(&self, k: usize) -> Vec<Self::Boolean>;

    ///
    /// Outputs the upper `k` bits of an `n`-bit element in big-endian representation.
    /// Enforces that the lower `n - k` bits are zero.
    ///
    fn to_upper_bits_be(&self, k: usize) -> Vec<Self::Boolean>;
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
