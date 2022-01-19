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
pub mod add_checked;
pub mod add_wrapped;
// pub mod sub;

use crate::{boolean::Boolean, traits::*, Environment, Mode};

use std::{
    fmt,
    marker::PhantomData,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign},
};

pub type I8<E> = Integer<E, i8>;
pub type I16<E> = Integer<E, i16>;
pub type I32<E> = Integer<E, i32>;
pub type I64<E> = Integer<E, i64>;
pub type I128<E> = Integer<E, i128>;

pub type U8<E> = Integer<E, u8>;
pub type U16<E> = Integer<E, u16>;
pub type U32<E> = Integer<E, u32>;
pub type U64<E> = Integer<E, u64>;
pub type U128<E> = Integer<E, u128>;

#[derive(Clone)]
pub struct Integer<E: Environment, I: IntegerType> {
    bits_le: Vec<Boolean<E>>,
    phantom: PhantomData<I>,
}

impl<E: Environment, I: IntegerType> IntegerTrait<I> for Integer<E, I> {
    /// Initializes a new integer.
    fn new(mode: Mode, value: I) -> Self {
        let mut bits_le = Vec::with_capacity(I::BITS);
        let mut value = value.to_le();
        for _ in 0..I::BITS {
            bits_le.push(Boolean::new(mode, value & I::one() == I::one()));
            value = value >> 1;
        }
        Self::from_bits(bits_le)
    }

    /// Returns `true` if the integer is a constant.
    fn is_constant(&self) -> bool {
        self.bits_le.iter().all(|bit| bit.is_constant() == true)
    }

    /// Ejects the integer as a constant integer value.
    fn eject_value(&self) -> I {
        self.bits_le.iter().rev().fold(I::zero(), |value, bit| {
            // TODO (@pranav) This explicit cast could be eliminated by using a trait bound
            //  `bool: AsPrimitive<I>`. This however requires the trait bound to be expressed
            //  for every implementation of Signed that uses `eject_value` which feels unclean.
            let bit_value = if bit.eject_value() { I::one() } else { I::zero() };
            (value << 1) ^ bit_value
        })
    }
}

impl<E: Environment, I: IntegerType> Integer<E, I> {
    /// Initialize a new integer from a vector of `Boolean`.
    pub(crate) fn from_bits(bits_le: Vec<Boolean<E>>) -> Self {
        if bits_le.len() != I::BITS {
            E::halt(format!(
                "Invalid integer format. Expected {} bits, found {} bits.",
                I::BITS,
                bits_le.len()
            ))
        } else {
            Self {
                bits_le,
                phantom: Default::default(),
            }
        }
    }
}

impl<E: Environment, I: IntegerType> fmt::Debug for Integer<E, I> {
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

    fn check_new<I: IntegerType, IC: IntegerTrait<I>>(mode: Mode)
    where
        Standard: Distribution<I>,
    {
        let expected: I = UniformRand::rand(&mut thread_rng());
        let candidate = IC::new(mode, expected);
        assert_eq!(mode.is_constant(), candidate.is_constant());
        assert_eq!(candidate.eject_value(), expected);
    }

    fn check_min_max<I: IntegerType, IC: IntegerTrait<I>>(mode: Mode) {
        assert_eq!(I::MIN, IC::new(mode, I::MIN).eject_value());
        assert_eq!(I::MAX, IC::new(mode, I::MAX).eject_value());
    }

    fn run_test<I: IntegerType>()
    where
        Standard: Distribution<I>,
    {
        for _ in 0..ITERATIONS {
            check_new::<I, Integer<Circuit, I>>(Mode::Constant);
            check_new::<I, Integer<Circuit, I>>(Mode::Public);
            check_new::<I, Integer<Circuit, I>>(Mode::Private);
        }

        check_min_max::<I, Integer<Circuit, I>>(Mode::Constant);
        check_min_max::<I, Integer<Circuit, I>>(Mode::Public);
        check_min_max::<I, Integer<Circuit, I>>(Mode::Private);
    }

    #[test]
    fn test_i8() {
        run_test::<i8>();
    }

    #[test]
    fn test_i16() {
        run_test::<i16>();
    }

    #[test]
    fn test_i32() {
        run_test::<i32>();
    }

    #[test]
    fn test_i64() {
        run_test::<i64>();
    }

    #[test]
    fn test_i128() {
        run_test::<i128>();
    }

    #[test]
    fn test_u8() {
        run_test::<u8>();
    }

    #[test]
    fn test_u16() {
        run_test::<u16>();
    }

    #[test]
    fn test_u32() {
        run_test::<u32>();
    }

    #[test]
    fn test_u64() {
        run_test::<u64>();
    }

    #[test]
    fn test_u128() {
        run_test::<u128>();
    }
}
