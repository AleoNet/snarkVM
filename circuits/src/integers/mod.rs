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

pub mod add;
pub mod add_checked;
pub mod add_wrapped;
pub mod equal;
pub mod from_bits;
pub mod neg;
pub mod one;
pub mod sub;
pub mod sub_checked;
pub mod sub_wrapped;
pub mod to_bits;
pub mod zero;

use crate::{
    boolean::Boolean,
    fields::BaseField,
    helpers::integers::*,
    traits::*,
    Environment,
    LinearCombination,
    Mode,
};

use std::{
    fmt,
    marker::PhantomData,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
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
        Self::from_bits_le(mode, &bits_le)
    }
}

impl<E: Environment, I: IntegerType> Eject for Integer<E, I> {
    type Primitive = I;

    ///
    /// Ejects the mode of the integer.
    ///
    fn eject_mode(&self) -> Mode {
        let mut integer_mode = Mode::Constant;
        for bit_mode in self.bits_le.iter().map(Eject::eject_mode) {
            // Check if the mode in the current iteration matches the integer mode.
            if integer_mode != bit_mode {
                // If they do not match, the integer mode must be a constant.
                // Otherwise, this is a malformed integer, and the program should halt.
                match integer_mode == Mode::Constant {
                    true => integer_mode = bit_mode,
                    false => E::halt("Detected an integer with a malformed mode"),
                }
            }
        }
        integer_mode
    }

    ///
    /// Ejects the integer as a constant integer value.
    ///
    fn eject_value(&self) -> Self::Primitive {
        self.bits_le.iter().rev().fold(I::zero(), |value, bit| match bit.eject_value() {
            true => (value << 1) ^ I::one(),
            false => (value << 1) ^ I::zero(),
        })
    }
}

impl<E: Environment, I: IntegerType> fmt::Debug for Integer<E, I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.eject_value())
    }
}

impl<E: Environment, I: IntegerType> From<Integer<E, I>> for LinearCombination<E::BaseField> {
    fn from(integer: Integer<E, I>) -> Self {
        From::from(&integer)
    }
}

impl<E: Environment, I: IntegerType> From<&Integer<E, I>> for LinearCombination<E::BaseField> {
    fn from(integer: &Integer<E, I>) -> Self {
        // Reconstruct the bits as a linear combination representing the original field value.
        let mut accumulator: LinearCombination<_> = BaseField::<E>::zero().into();
        let mut coefficient = BaseField::one();
        for bit in &integer.bits_le {
            accumulator += LinearCombination::from(BaseField::from(bit) * &coefficient);
            coefficient = coefficient.double();
        }
        accumulator
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 1000;

    fn check_new<I: IntegerType, IC: IntegerTrait<I>>(mode: Mode) {
        let expected: I = UniformRand::rand(&mut thread_rng());
        let candidate = IC::new(mode, expected);
        assert_eq!(mode.is_constant(), candidate.is_constant());
        assert_eq!(candidate.eject_value(), expected);
    }

    fn check_min_max<I: IntegerType, IC: IntegerTrait<I>>(mode: Mode) {
        assert_eq!(I::MIN, IC::new(mode, I::MIN).eject_value());
        assert_eq!(I::MAX, IC::new(mode, I::MAX).eject_value());
    }

    fn run_test<I: IntegerType>() {
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
