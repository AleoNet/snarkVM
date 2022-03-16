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

use crate::prelude::*;

/// Representation of an integer.
pub trait IntegerTrait<
    B: BooleanTrait,
    I: IntegerType,
    U8: IntegerCore<B, u8>,
    U16: IntegerCore<B, u16>,
    U32: IntegerCore<B, u32>,
>:
    IntegerCore<B, I>
    + PowChecked<U8, Output = Self>
    + PowWrapped<U8, Output = Self>
    + Shl<U8, Output = Self>
    + ShlAssign<U8>
    + ShlChecked<U8, Output = Self>
    + ShlWrapped<U8, Output = Self>
    + Shr<U8, Output = Self>
    + ShrAssign<U8>
    + ShrChecked<U8, Output = Self>
    + ShrWrapped<U8, Output = Self>
    + PowChecked<U16, Output = Self>
    + PowWrapped<U16, Output = Self>
    + Shl<U16, Output = Self>
    + ShlAssign<U16>
    + ShlChecked<U16, Output = Self>
    + ShlWrapped<U16, Output = Self>
    + Shr<U16, Output = Self>
    + ShrAssign<U16>
    + ShrChecked<U16, Output = Self>
    + ShrWrapped<U16, Output = Self>
    + PowChecked<U32, Output = Self>
    + PowWrapped<U32, Output = Self>
    + Shl<U32, Output = Self>
    + ShlAssign<U32>
    + ShlChecked<U32, Output = Self>
    + ShlWrapped<U32, Output = Self>
    + Shr<U32, Output = Self>
    + ShrAssign<U32>
    + ShrChecked<U32, Output = Self>
    + ShrWrapped<U32, Output = Self>
{
}

pub trait IntegerCore<B: BooleanTrait, I: IntegerType>:
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
    + Compare
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
    + Parser
    + SubAssign
    + Sub<Output = Self>
    + SubChecked<Output = Self>
    + SubWrapped<Output = Self>
    + Ternary
    + ToBits
    + Zero
{
}

pub(super) mod integer_type {
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

    pub trait CheckedPow: Sized {
        fn checked_pow(&self, v: u32) -> Option<Self>;
    }

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

        /// Returns the absolute value of the integer type.
        fn absolute(&self) -> Self;
    }

    macro_rules! integer_properties_impl {
        ($t:ty, $dual:ty, $is_signed:expr, $abs:expr) => {
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

                #[inline]
                fn absolute(&self) -> Self {
                    $abs(self)
                }
            }
        };
    }

    integer_properties_impl!(u8, i8, false, |i: &u8| *i);
    integer_properties_impl!(u16, i16, false, |i: &u16| *i);
    integer_properties_impl!(u32, i32, false, |i: &u32| *i);
    integer_properties_impl!(u64, i64, false, |i: &u64| *i);
    integer_properties_impl!(u128, i128, false, |i: &u128| *i);
    integer_properties_impl!(i8, u8, true, |i: &i8| i.abs());
    integer_properties_impl!(i16, u16, true, |i: &i16| i.abs());
    integer_properties_impl!(i32, u32, true, |i: &i32| i.abs());
    integer_properties_impl!(i64, u64, true, |i: &i64| i.abs());
    integer_properties_impl!(i128, u128, true, |i: &i128| i.abs());
}

/// Sealed trait pattern to prevent abuse of Magnitude.
pub(super) mod magnitude {
    use super::integer_type::IntegerType;
    use num_traits::{ToPrimitive, Unsigned};

    /// Trait for integers that can be used as an unsigned magnitude.
    /// `Magnitude`s are either used to represent an integer exponent
    /// or the right operand in integer shift operations.
    pub trait Magnitude: IntegerType + ToPrimitive + Unsigned {}
    impl Magnitude for u8 {}
    impl Magnitude for u16 {}
    impl Magnitude for u32 {}
}
