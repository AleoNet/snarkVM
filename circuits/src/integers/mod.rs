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

pub mod helpers;

pub mod add;
// pub mod div;
// pub mod equal;
// pub mod less_than;
// pub mod sub;
// pub mod ternary;

use crate::{boolean::Boolean, traits::*, Environment, Mode};

use num_traits::{
    Bounded,
    NumCast,
    One as NumOne,
    PrimInt,
    WrappingAdd,
    WrappingMul,
    WrappingNeg,
    WrappingSub,
    Zero as NumZero,
};
use snarkvm_utilities::ops::Div;
use std::{
    fmt,
    fmt::{Debug, Display},
    marker::PhantomData,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
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

pub type I8<E> = Integer<E, i8, { i8::BITS as usize }>;
pub type I16<E> = Integer<E, i16, { i16::BITS as usize }>;
pub type I32<E> = Integer<E, i32, { i32::BITS as usize }>;
pub type I64<E> = Integer<E, i64, { i64::BITS as usize }>;
pub type I128<E> = Integer<E, i128, { i128::BITS as usize }>;

pub type U8<E> = Integer<E, u8, { u8::BITS as usize }>;
pub type U16<E> = Integer<E, u16, { u16::BITS as usize }>;
pub type U32<E> = Integer<E, u32, { u32::BITS as usize }>;
pub type U64<E> = Integer<E, u64, { u64::BITS as usize }>;
pub type U128<E> = Integer<E, u128, { u128::BITS as usize }>;

#[derive(Clone)]
pub struct Integer<E: Environment, I: IntegerType, const BITS: usize> {
    bits_le: Vec<Boolean<E>>,
    phantom: PhantomData<I>,
}

impl<E: Environment, I: IntegerType, const BITS: usize> IntegerTrait for Integer<E, I, BITS> {}

impl<E: Environment, I: IntegerType, const BITS: usize> Integer<E, I, BITS> {
    /// Initializes a new integer.
    pub fn new(mode: Mode, value: I) -> Self {
        let mut bits_le = Vec::with_capacity(BITS);
        let mut value = value.to_le();
        for _ in 0..BITS {
            bits_le.push(Boolean::new(mode, value & I::one() == I::one()));
            value = value >> 1;
        }
        Self::from_bits(bits_le)
    }

    /// Initialize a new integer from a vector of Booleans.
    pub(crate) fn from_bits(bits_le: Vec<Boolean<E>>) -> Self {
        if bits_le.len() != BITS {
            E::halt(format!(
                "Invalid integer format. Expected {} bits, found {} bits.",
                BITS,
                bits_le.len()
            ))
        } else {
            Self {
                bits_le,
                phantom: Default::default(),
            }
        }
    }

    /// Returns `true` if the integer is a constant.
    pub fn is_constant(&self) -> bool {
        self.bits_le.iter().all(|bit| bit.is_constant() == true)
    }

    /// Ejects the unsigned integer as a constant unsigned integer value.
    pub fn eject_value(&self) -> I {
        self.bits_le.iter().rev().fold(I::zero(), |value, bit| {
            // TODO (@pranav) This explicit cast could be eliminated by using a trait bound
            //  `bool: AsPrimitive<I>`. This however requires the trait bound to be expressed
            //  for every implementation of Signed that uses `eject_value` which feels unclean.
            let bit_value = if bit.eject_value() { I::one() } else { I::zero() };
            (value << 1) ^ bit_value
        })
    }
}

impl<E: Environment, I: IntegerType, const BITS: usize> fmt::Debug for Integer<E, I, BITS> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.eject_value())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::{
        distributions::{Distribution, Standard},
        thread_rng,
    };

    const ITERATIONS: usize = 1000;

    fn run_test<E: Environment, I: IntegerType, const BITS: usize>(mode: Mode)
    where
        Standard: Distribution<I>,
    {
        for _ in 0..ITERATIONS {
            let value: I = UniformRand::rand(&mut thread_rng());
            let integer = Integer::<Circuit, I, BITS>::new(mode, value);
            assert_eq!(mode.is_constant(), integer.is_constant());
            assert_eq!(integer.eject_value(), value);
        }

        assert_eq!(
            Integer::<Circuit, I, BITS>::new(mode, I::min_value()).eject_value(),
            I::min_value()
        );
        assert_eq!(
            Integer::<Circuit, I, BITS>::new(mode, I::max_value()).eject_value(),
            I::max_value()
        );
    }

    #[test]
    fn test_i8() {
        run_test::<Circuit, i8, 8>(Mode::Constant);
        run_test::<Circuit, i8, 8>(Mode::Public);
        run_test::<Circuit, i8, 8>(Mode::Private);
    }

    #[test]
    fn test_i16() {
        run_test::<Circuit, i16, 16>(Mode::Constant);
        run_test::<Circuit, i16, 16>(Mode::Public);
        run_test::<Circuit, i16, 16>(Mode::Private);
    }

    #[test]
    fn test_i32() {
        run_test::<Circuit, i32, 32>(Mode::Constant);
        run_test::<Circuit, i32, 32>(Mode::Public);
        run_test::<Circuit, i32, 32>(Mode::Private);
    }

    #[test]
    fn test_i64() {
        run_test::<Circuit, i64, 64>(Mode::Constant);
        run_test::<Circuit, i64, 64>(Mode::Public);
        run_test::<Circuit, i64, 64>(Mode::Private);
    }

    #[test]
    fn test_i128() {
        run_test::<Circuit, i128, 128>(Mode::Constant);
        run_test::<Circuit, i128, 128>(Mode::Public);
        run_test::<Circuit, i128, 128>(Mode::Private);
    }

    #[test]
    fn test_u8() {
        run_test::<Circuit, u8, 8>(Mode::Constant);
        run_test::<Circuit, u8, 8>(Mode::Public);
        run_test::<Circuit, u8, 8>(Mode::Private);
    }

    #[test]
    fn test_u16() {
        run_test::<Circuit, u16, 16>(Mode::Constant);
        run_test::<Circuit, u16, 16>(Mode::Public);
        run_test::<Circuit, u16, 16>(Mode::Private);
    }

    #[test]
    fn test_u32() {
        run_test::<Circuit, u32, 32>(Mode::Constant);
        run_test::<Circuit, u32, 32>(Mode::Public);
        run_test::<Circuit, u32, 32>(Mode::Private);
    }

    #[test]
    fn test_u64() {
        run_test::<Circuit, u64, 64>(Mode::Constant);
        run_test::<Circuit, u64, 64>(Mode::Public);
        run_test::<Circuit, u64, 64>(Mode::Private);
    }

    #[test]
    fn test_u128() {
        run_test::<Circuit, u128, 128>(Mode::Constant);
        run_test::<Circuit, u128, 128>(Mode::Public);
        run_test::<Circuit, u128, 128>(Mode::Private);
    }
}
