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

pub(crate) mod integers {
    use num_traits::{
        CheckedNeg,
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
        ops::Div,
    };

    /// Trait bound for integer values. Common to both signed and unsigned integers.
    pub trait IntegerType:
        'static
        + CheckedNeg
        + Debug
        + Display
        + NumZero
        + NumOne
        + WrappingAdd
        + WrappingMul
        + WrappingNeg
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

    macro_rules! integer_properties_impl {
        ($t:ty, $is_signed:expr) => {
            impl IntegerProperties for $t {
                const BITS: usize = <$t>::BITS as usize;
                const MAX: $t = <$t>::MAX;
                const MIN: $t = <$t>::MIN;

                #[inline]
                fn is_signed() -> bool {
                    $is_signed
                }
            }
        };
    }

    integer_properties_impl!(u8, false);
    integer_properties_impl!(u16, false);
    integer_properties_impl!(u32, false);
    integer_properties_impl!(u64, false);
    integer_properties_impl!(u128, false);
    integer_properties_impl!(i8, true);
    integer_properties_impl!(i16, true);
    integer_properties_impl!(i32, true);
    integer_properties_impl!(i64, true);
    integer_properties_impl!(i128, true);

    /// Properties common to all integer types.
    /// Note that `PrimInt` implements `Bounded` which implements
    /// `min_value` and `max_value`.
    pub trait IntegerProperties: PrimInt + Debug + Display {
        /// Returns the number of bits required to represent this integer.
        const BITS: usize;
        /// Returns the maximum value representable by this integer.
        const MAX: Self;
        /// Returns the minimum value representable by this integer.
        const MIN: Self;

        /// Returns `true` if Self is a primitive signed integer and `false` otherwise.
        fn is_signed() -> bool;
    }
}
