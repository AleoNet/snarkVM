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

use crate::{Environment, Mode};

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
use nom::{error::VerboseError, IResult};
use num_traits::Inv;

pub use crate::traits::{
    integers::{CheckedPow, IntegerProperties, IntegerType, WrappingDiv, WrappingPow, WrappingRem},
    private::Magnitude,
};
pub use snarkvm_fields::{Field as F, One as O, PrimeField, Zero as Z};

pub use itertools::Itertools;

/// Representation of a boolean.
pub trait BooleanTrait:
    Adder
    + BitAndAssign
    + BitAnd<Output = Self>
    + BitOrAssign
    + BitOr<Output = Self>
    + BitXorAssign
    + BitXor<Output = Self>
    + Clone
    + DataType<Self>
    + Debug
    + Eject<Primitive = bool>
    + Equal
    + FromBits
    + Inject<Primitive = bool>
    + Nand
    + Nor
    + Not
    + Parser
    + Subtractor
    + Ternary
    + ToBits
{
}

/// Representation of a base field element.
pub trait FieldTrait<B: BooleanTrait>:
    Add<Output = Self>
    + AddAssign
    + Clone
    + DataType<B>
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

/// Representation of a group element.
pub trait GroupTrait<B: BooleanTrait, S: ScalarTrait<B>>:
    Add<Output = Self>
    + AddAssign
    + Clone
    + DataType<B>
    + Debug
    + Double<Output = Self>
    + Eject
    + Equal
    + Inject
    + Mul<S, Output = Self>
    + MulAssign<S>
    + Neg<Output = Self>
    + Parser
    + Sub<Output = Self>
    + SubAssign
    + Ternary
    + Zero
{
}

/// Representation of an integer.
pub trait IntegerTrait<B: BooleanTrait, I: IntegerType>:
    AddAssign
    + Add<Output = Self>
    + AddChecked<Output = Self>
    + AddWrapped<Output = Self>
    + BitAndAssign
    + BitAnd<Output = Self>
    + BitOrAssign
    + BitOr<Output = Self>
    + BitXorAssign
    + BitXor<Output = Self>
    + Clone
    + DataType<B>
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
    + SubAssign
    + Sub<Output = Self>
    + SubChecked<Output = Self>
    + SubWrapped<Output = Self>
    + Ternary
    + ToBits
    + Zero
{
}

pub trait IntegerMagnitude<B: BooleanTrait, I: IntegerType, IM: Magnitude, M: IntegerTrait<B, IM>>:
    IntegerTrait<B, I>
    + PowChecked<M, Output = Self>
    + PowWrapped<M, Output = Self>
    + Shl<M, Output = Self>
    + ShlAssign<M>
    + ShlChecked<M, Output = Self>
    + ShlWrapped<M, Output = Self>
    + Shr<M, Output = Self>
    + ShrAssign<M>
    + ShrChecked<M, Output = Self>
    + ShrWrapped<M, Output = Self>
{
}

/// Representation of a scalar field element.
pub trait ScalarTrait<B: BooleanTrait>:
    Clone + DataType<B> + Debug + Eject + Equal + Inject + One + Parser + Ternary + ToBits + Zero
{
}

/// Operations to convert to and from bit representation in a circuit environment.
pub trait DataType<B: BooleanTrait>: FromBits<Boolean = B> + ToBits<Boolean = B> {}

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
    /// Ejects the mode and primitive value of the circuit type.
    ///
    fn eject(&self) -> (Mode, Self::Primitive) {
        (self.eject_mode(), self.eject_value())
    }

    ///
    /// Ejects the mode of the circuit type.
    ///
    fn eject_mode(&self) -> Mode;

    ///
    /// Ejects the circuit type as a primitive value.
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

pub type ParserResult<'a, O> = IResult<&'a str, O, VerboseError<&'a str>>;

/// Operations to parse a string literal into an object.
pub trait Parser: Display {
    type Environment: Environment;

    ///
    /// Returns the type name of the object as a string. (i.e. "u8")
    ///
    fn type_name() -> &'static str;

    ///
    /// Parses a string literal into an object.
    ///
    fn parse(s: &str) -> ParserResult<Self>
    where
        Self: Sized;

    ///
    /// Returns an object from a string literal.
    ///
    fn from_str(string: &str) -> Self
    where
        Self: Sized,
    {
        match Self::parse(string) {
            Ok((_, circuit)) => circuit,
            Err(error) => Self::Environment::halt(format!("Failed to parse {}: {}", Self::type_name(), error)),
        }
    }
}

pub trait ToField {
    type Boolean: BooleanTrait;
    type Field: FieldTrait<Self::Boolean>;

    /// Casts a scalar field element into a base field element.
    fn to_field(&self) -> Self::Field;
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

    fn from_bits_le(mode: Mode, bits_le: &[Self::Boolean]) -> Self
    where
        Self: Sized;

    fn from_bits_be(mode: Mode, bits_be: &[Self::Boolean]) -> Self
    where
        Self: Sized;
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

pub(crate) mod integers {
    use snarkvm_utilities::{FromBytes, ToBytes, UniformRand};

    use core::{
        fmt::{Debug, Display},
        num::ParseIntError,
        ops::{Div, Rem},
        str::FromStr,
    };
    use num_traits::{
        CheckedNeg,
        CheckedShl,
        CheckedShr,
        One as NumOne,
        PrimInt,
        ToPrimitive,
        WrappingAdd,
        WrappingMul,
        WrappingNeg,
        WrappingShl,
        WrappingShr,
        WrappingSub,
        Zero as NumZero,
    };

    /// Trait bound for integer values. Common to both signed and unsigned integers.
    pub trait IntegerType:
        'static
        + CheckedNeg
        + CheckedPow
        + CheckedShl
        + CheckedShr
        + Debug
        + Default
        + Display
        + FromBytes
        + FromStr<Err = ParseIntError>
        + NumZero
        + NumOne
        + ToBytes
        + ToPrimitive
        + UniformRand
        + WrappingAdd
        + WrappingMul
        + WrappingNeg
        + WrappingPow
        + WrappingRem
        + WrappingShl
        + WrappingShr
        + WrappingSub
        + WrappingDiv
        + IntegerProperties
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

    macro_rules! checked_impl {
        ($trait_name:ident, $method:ident, $t:ty) => {
            impl $trait_name for $t {
                #[inline]
                fn $method(&self, rhs: u32) -> Option<$t> {
                    <$t>::$method(*self, rhs)
                }
            }
        };
    }

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
            impl $trait_name for $t {
                #[inline]
                fn $method(&self, v: $rhs) -> Self {
                    <$t>::$method(*self, v)
                }
            }
        };
    }

    macro_rules! integer_properties_impl {
        ($t:ty, $dual:ty, $is_signed:expr) => {
            impl IntegerProperties for $t {
                type Dual = $dual;

                const BITS: usize = <$t>::BITS as usize;
                const MAX: $t = <$t>::MAX;
                const MIN: $t = <$t>::MIN;

                #[inline]
                fn is_signed() -> bool {
                    $is_signed
                }

                #[inline]
                fn type_name() -> &'static str {
                    std::any::type_name::<$t>()
                }
            }
        };
    }

    pub trait CheckedPow: Sized {
        fn checked_pow(&self, v: u32) -> Option<Self>;
    }

    checked_impl!(CheckedPow, checked_pow, u8);
    checked_impl!(CheckedPow, checked_pow, u16);
    checked_impl!(CheckedPow, checked_pow, u32);
    checked_impl!(CheckedPow, checked_pow, u64);
    checked_impl!(CheckedPow, checked_pow, u128);
    checked_impl!(CheckedPow, checked_pow, i8);
    checked_impl!(CheckedPow, checked_pow, i16);
    checked_impl!(CheckedPow, checked_pow, i32);
    checked_impl!(CheckedPow, checked_pow, i64);
    checked_impl!(CheckedPow, checked_pow, i128);

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

    pub trait WrappingRem: Sized + Rem<Self, Output = Self> {
        fn wrapping_rem(&self, v: &Self) -> Self;
    }

    wrapping_impl!(WrappingRem, wrapping_rem, u8);
    wrapping_impl!(WrappingRem, wrapping_rem, u16);
    wrapping_impl!(WrappingRem, wrapping_rem, u32);
    wrapping_impl!(WrappingRem, wrapping_rem, u64);
    wrapping_impl!(WrappingRem, wrapping_rem, u128);
    wrapping_impl!(WrappingRem, wrapping_rem, i8);
    wrapping_impl!(WrappingRem, wrapping_rem, i16);
    wrapping_impl!(WrappingRem, wrapping_rem, i32);
    wrapping_impl!(WrappingRem, wrapping_rem, i64);
    wrapping_impl!(WrappingRem, wrapping_rem, i128);

    pub trait WrappingPow: Sized {
        fn wrapping_pow(&self, v: u32) -> Self;
    }

    wrapping_impl!(WrappingPow, wrapping_pow, u8, u32);
    wrapping_impl!(WrappingPow, wrapping_pow, u16, u32);
    wrapping_impl!(WrappingPow, wrapping_pow, u32, u32);
    wrapping_impl!(WrappingPow, wrapping_pow, u64, u32);
    wrapping_impl!(WrappingPow, wrapping_pow, u128, u32);
    wrapping_impl!(WrappingPow, wrapping_pow, i8, u32);
    wrapping_impl!(WrappingPow, wrapping_pow, i16, u32);
    wrapping_impl!(WrappingPow, wrapping_pow, i32, u32);
    wrapping_impl!(WrappingPow, wrapping_pow, i64, u32);
    wrapping_impl!(WrappingPow, wrapping_pow, i128, u32);

    /// Properties common to all integer types.
    pub trait IntegerProperties: PrimInt + Debug + Display {
        type Dual: IntegerType;
        /// Returns the number of bits required to represent this integer.
        const BITS: usize;
        /// Returns the maximum value representable by this integer.
        const MAX: Self;
        /// Returns the minimum value representable by this integer.
        const MIN: Self;

        /// Returns `true` if `Self` is a signed integer and `false` otherwise.
        fn is_signed() -> bool;

        /// Returns the name of the integer type as a string slice. (i.e. "u8")
        fn type_name() -> &'static str;
    }

    integer_properties_impl!(u8, i8, false);
    integer_properties_impl!(u16, i16, false);
    integer_properties_impl!(u32, i32, false);
    integer_properties_impl!(u64, i64, false);
    integer_properties_impl!(u128, i128, false);
    integer_properties_impl!(i8, u8, true);
    integer_properties_impl!(i16, u16, true);
    integer_properties_impl!(i32, u32, true);
    integer_properties_impl!(i64, u64, true);
    integer_properties_impl!(i128, u128, true);
}

/// Sealed trait pattern to prevent abuse of Magnitude.
mod private {
    use crate::traits::integers::IntegerType;
    use num_traits::{ToPrimitive, Unsigned};

    /// Trait for integers that can be used as an unsigned magnitude.
    /// `Magnitude`s are either used to represent an integer exponent
    /// or the right operand in integer shift operations.
    pub trait Magnitude: IntegerType + ToPrimitive + Unsigned {}
    impl Magnitude for u8 {}
    impl Magnitude for u16 {}
    impl Magnitude for u32 {}
}
