// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::Mode;

use num_traits::{
    Bounded,
    Inv,
    NumCast,
    One as NumOne,
    PrimInt,
    WrappingAdd,
    WrappingMul,
    WrappingNeg,
    WrappingSub,
    Zero as NumZero,
};
use std::{
    fmt::{Debug, Display},
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Not, Sub, SubAssign},
};

// TODO (@pranav) Find a better place for this
//   Taken from/extending num_traits
macro_rules! wrapping_impl {
    ($trait_name:ident, $method:ident, $t:ty) => {
        impl $trait_name for $t {
            #[inline]
            fn $method(&self, v: &Self) -> Self {
                <$t>::$method(*self, *v)
            }
        }
    };
    ($trait_name:ident, $method:ident, $t:ty, $rhs:ty) => {
        impl $trait_name<$rhs> for $t {
            #[inline]
            fn $method(&self, v: &$rhs) -> Self {
                <$t>::$method(*self, *v)
            }
        }
    };
}

pub trait WrappingDiv: Sized + Div<Self, Output = Self> {
    fn wrapping_div(&self, v: &Self) -> Self;
}

wrapping_impl!(WrappingDiv, wrapping_div, u8);
wrapping_impl!(WrappingDiv, wrapping_div, u16);
wrapping_impl!(WrappingDiv, wrapping_div, u32);
wrapping_impl!(WrappingDiv, wrapping_div, u64);
wrapping_impl!(WrappingDiv, wrapping_div, u128);
wrapping_impl!(WrappingDiv, wrapping_div, i8);
wrapping_impl!(WrappingDiv, wrapping_div, i16);
wrapping_impl!(WrappingDiv, wrapping_div, i32);
wrapping_impl!(WrappingDiv, wrapping_div, i64);
wrapping_impl!(WrappingDiv, wrapping_div, i128);

/// Trait bound for integer values. Common to both signed and unsigned integers.
pub trait IntegerType:
    'static
    + Debug
    + Display
    + PrimInt
    + Bounded
    + NumZero
    + NumOne
    + WrappingAdd
    + WrappingMul
    + WrappingNeg
    + WrappingSub
    + WrappingDiv
    + NumCast
{
}

impl IntegerType for i8 {}
impl IntegerType for i16 {}
impl IntegerType for i32 {}
impl IntegerType for i64 {}
impl IntegerType for i128 {}

impl IntegerType for u8 {}
impl IntegerType for u16 {}
impl IntegerType for u32 {}
impl IntegerType for u64 {}
impl IntegerType for u128 {}

/// Representation of a boolean.
pub trait BooleanTrait: And + Clone + Debug + Equal + Nand + Nor + Not + Or + Ternary + Xor {}

/// Representation of a base field.
pub trait BaseFieldTrait:
    Add
    + AddAssign
    + Clone
    + Debug
    + Div
    + DivAssign
    + Double
    + Equal
    + Inv
    + Mul
    + MulAssign
    + Neg
    + One
    + Square
    + Sub
    + SubAssign
    + Ternary
    + ToBits
    + Zero
{
}

/// Representation of an integer.
pub trait IntegerTrait<I: IntegerType>: Add + AddAssign + Clone + Debug
// + Div
// + DivAssign
// + Double
// + Equal
// + Inv
// + Mul
// + MulAssign
// + Neg
// + One
// + Square
// + Sub
// + SubAssign
// + Ternary
// + ToBits
// + Zero
{
    /// Initializes a new integer.
    fn new(mode: Mode, value: I) -> Self;

    /// Returns `true` if the integer is a constant.
    fn is_constant(&self) -> bool;

    /// Ejects the unsigned integer as a constant unsigned integer value.
    fn eject_value(&self) -> I;
}

// TODO why not use num_traits::Zero?
/// Representation of the zero value.
pub trait Zero {
    type Boolean: BooleanTrait;
    type Output;

    /// Returns a new zero constant.
    fn zero() -> Self;

    /// Returns `true` if `self` is zero.
    fn is_zero(&self) -> Self::Output;
}

/// Representation of the one value.
pub trait One {
    type Boolean: BooleanTrait;
    type Output;

    /// Returns a new one constant.
    fn one() -> Self;

    /// Returns `true` if `self` is one.
    fn is_one(&self) -> Self::Output;
}

/// Trait for equality comparisons.
pub trait Equal<Rhs: ?Sized = Self> {
    type Boolean: BooleanTrait;
    type Output;

    /// Returns `true` if `self` and `other` are equal.
    fn is_eq(&self, other: &Rhs) -> Self::Output;

    /// Returns `true` if `self` and `other` are *not* equal.
    fn is_neq(&self, other: &Rhs) -> Self::Output;
}

pub trait LessThan<Rhs: ?Sized = Self> {
    type Boolean: BooleanTrait;
    type Output;

    /// Returns `true` if `self` is less than `other`.
    fn is_lt(&self, other: &Rhs) -> Self::Output;
}

/// Binary operator for performing `a AND b`.
pub trait And<Rhs: ?Sized = Self> {
    type Boolean: BooleanTrait;
    type Output;

    /// Returns `(a AND b)`.
    fn and(&self, other: &Rhs) -> Self::Output;
}

/// Binary operator for performing `a OR b`.
pub trait Or<Rhs: ?Sized = Self> {
    type Boolean: BooleanTrait;
    type Output;

    /// Returns `(a OR b)`.
    fn or(&self, other: &Rhs) -> Self::Output;
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

/// Binary operator for performing `(a != b)`.
pub trait Xor<Rhs: ?Sized = Self> {
    type Boolean: BooleanTrait;
    type Output;

    /// Returns `(a != b)`.
    fn xor(&self, other: &Rhs) -> Self::Output;
}

/// Trait for ternary operations.
pub trait Ternary {
    type Boolean: BooleanTrait;
    type Output;

    /// Returns `first` if `condition` is `true`, otherwise returns `second`.
    fn ternary(condition: &Self::Boolean, first: &Self, second: &Self) -> Self::Output;
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

/// Unary operator for converting to bits.
pub trait ToBits {
    type Boolean: BooleanTrait;

    fn to_bits_le(&self) -> Vec<Self::Boolean>;

    fn to_bits_be(&self) -> Vec<Self::Boolean>;
}
