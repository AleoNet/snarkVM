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

use super::*;

impl<E: Environment, I: IntegerType> Mul<Integer<E, I>> for Integer<E, I> {
    type Output = Self;

    fn mul(self, other: Self) -> Self::Output {
        self * &other
    }
}

impl<E: Environment, I: IntegerType> Mul<Integer<E, I>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn mul(self, other: Integer<E, I>) -> Self::Output {
        self * &other
    }
}

impl<E: Environment, I: IntegerType> Mul<&Integer<E, I>> for Integer<E, I> {
    type Output = Self;

    fn mul(self, other: &Self) -> Self::Output {
        &self * other
    }
}

impl<E: Environment, I: IntegerType> Mul<&Integer<E, I>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn mul(self, other: &Integer<E, I>) -> Self::Output {
        let mut output = self.clone();
        output *= other;
        output
    }
}

impl<E: Environment, I: IntegerType> MulAssign<Integer<E, I>> for Integer<E, I> {
    fn mul_assign(&mut self, other: Integer<E, I>) {
        *self *= &other;
    }
}

impl<E: Environment, I: IntegerType> MulAssign<&Integer<E, I>> for Integer<E, I> {
    fn mul_assign(&mut self, other: &Integer<E, I>) {
        // Stores the product of `self` and `other` in `self`.
        *self = self.mul_checked(other);
    }
}

impl<E: Environment, I: IntegerType> MulChecked<Self> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn mul_checked(&self, other: &Integer<E, I>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the product and return the new constant.
            match self.eject_value().checked_mul(&other.eject_value()) {
                Some(value) => Integer::new(Mode::Constant, value),
                None => E::halt("Integer overflow on multiplication of two constants"),
            }
        } else if I::is_signed() {
            // Multiply the absolute value of `self` and `other` in the base field.
            let absolute_self = Self::ternary(self.msb(), &Self::zero().sub_wrapped(self), self);
            let absolute_other = Self::ternary(other.msb(), &Self::zero().sub_wrapped(other), other);
            let mut bits_le = Self::mul_bits(&absolute_self.bits_le, &absolute_other.bits_le, true);

            // We need to check that the abs(a) * abs(b) did not exceed the unsigned maximum.
            let carry_bits_nonzero = bits_le[I::BITS..].iter().fold(Boolean::new(Mode::Constant, false), |a, b| a | b);

            // If the product should be positive, then it cannot exceed the signed maximum.
            let product_msb = &bits_le[I::BITS - 1];
            let operands_same_sign = &self.msb().is_eq(other.msb());
            let positive_product_overflows = operands_same_sign & product_msb;

            // If the product should be negative, then it cannot exceed the absolute value of the signed minimum.
            let negative_product_underflows = {
                let lower_product_bits_nonzero =
                    bits_le[..(I::BITS - 1)].iter().fold(Boolean::new(Mode::Constant, false), |a, b| a | b);
                let negative_product_lt_or_eq_signed_min = !product_msb | (product_msb & !lower_product_bits_nonzero);
                !operands_same_sign & !negative_product_lt_or_eq_signed_min
            };

            // Ensure there are no overflows.
            let overflow = carry_bits_nonzero | positive_product_overflows | negative_product_underflows;
            E::assert_eq(overflow, E::zero());

            // Remove carry bits.
            bits_le.truncate(I::BITS);

            // Return the product of `self` and `other` with the appropriate sign.
            let product = Integer { bits_le, phantom: Default::default() };
            Self::ternary(operands_same_sign, &product, &Self::zero().sub_wrapped(&product))
        } else {
            let mut bits_le = Self::mul_bits(&self.bits_le, &other.bits_le, true);

            // For unsigned multiplication, check that none of the carry bits are set.
            let overflow = bits_le[I::BITS..].iter().fold(Boolean::new(Mode::Constant, false), |a, b| a | b);
            E::assert_eq(overflow, E::zero());

            // Remove carry bits.
            bits_le.truncate(I::BITS);

            // Return the product of `self` and `other`.
            Integer { bits_le, phantom: Default::default() }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;
    use test_utilities::*;

    use rand::thread_rng;
    use std::{ops::RangeInclusive, panic::RefUnwindSafe};

    const ITERATIONS: usize = 128;

    #[rustfmt::skip]
    fn check_mul<I: IntegerType + std::panic::RefUnwindSafe>(
        name: &str,
        first: I,
        second: I,
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);
        let case = format!("({} * {})", a.eject_value(), b.eject_value());
        match first.checked_mul(&second) {
            Some(value) => {
                check_operation_passes(name, &case, value, &a, &b, Integer::mul_checked, num_constants, num_public, num_private, num_constraints);
                // Commute the operation.
                let a = Integer::<Circuit, I>::new(mode_a, second);
                let b = Integer::<Circuit, I>::new(mode_b, first);
                check_operation_passes(name, &case, value, &a, &b, Integer::mul_checked, num_constants, num_public, num_private, num_constraints);
            },
            None => {
                match (mode_a, mode_b) {
                    (Mode::Constant, Mode::Constant) => {
                        check_operation_halts(&a, &b, Integer::mul_checked);
                        // Commute the operation.
                        let a = Integer::<Circuit, I>::new(mode_a, second);
                        let b = Integer::<Circuit, I>::new(mode_b, first);
                        check_operation_halts(&a, &b, Integer::mul_checked);
                    },
                    _ => {
                        check_operation_fails(name, &case, &a, &b, Integer::mul_checked, num_constants, num_public, num_private, num_constraints);
                        // Commute the operation.
                        let a = Integer::<Circuit, I>::new(mode_a, second);
                        let b = Integer::<Circuit, I>::new(mode_b, first);
                        check_operation_fails(name, &case, &a, &b, Integer::mul_checked, num_constants, num_public, num_private, num_constraints);
                    }
                }
            }
        }
    }

    #[rustfmt::skip]
    fn run_test<I: IntegerType + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let check_mul = | name: &str, first: I, second: I | check_mul(name, first, second, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);

        for i in 0..ITERATIONS {
            // TODO (@pranav) Uniform random sampling almost always produces arguments that result in an overflow.
            //  Is there a better method for sampling arguments?
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: I = UniformRand::rand(&mut thread_rng());

            let name = format!("Mul: {} * {} {}", mode_a, mode_b, i);
            check_mul(&name, first, second);

            let name = format!("Double: {} * {} {}", mode_a, mode_b, i);
            check_mul(&name, first, I::one() + I::one());

            let name = format!("Square: {} * {} {}", mode_a, mode_b, i);
            check_mul(&name, first, first);
        }

        // Check specific cases common to signed and unsigned integers.
        check_mul("1 * MAX", I::one(), I::MAX);
        check_mul("MAX * 1", I::MAX, I::one());
        check_mul("1 * MIN",I::one(), I::MIN);
        check_mul("MIN * 1",I::MIN, I::one());
        check_mul("0 * MAX", I::zero(), I::MAX);
        check_mul( "MAX * 0", I::MAX, I::zero());
        check_mul( "0 * MIN", I::zero(), I::MIN);
        check_mul( "MIN * 0", I::MIN, I::zero());
        check_mul("1 * 1", I::one(), I::one());

        // Check common overflow cases.
        check_mul("MAX * 2", I::MAX, I::one() + I::one());
        check_mul("2 * MAX", I::one() + I::one(), I::MAX);

        // Check additional corner cases for signed integers.
        if I::is_signed() {
            check_mul("MAX * -1", I::MAX, I::zero() - I::one());
            check_mul("-1 * MAX", I::zero() - I::one(), I::MAX);

            check_mul("MIN * -1", I::MIN, I::zero() - I::one());
            check_mul("-1 * MIN", I::zero() - I::one(), I::MIN);
            check_mul("MIN * -2", I::MIN, I::zero() - I::one() - I::one());
            check_mul("-2 * MIN", I::zero() - I::one() - I::one(), I::MIN);
        }
    }

    #[rustfmt::skip]
    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) where
        RangeInclusive<I>: Iterator<Item = I>,
    {
        for first in I::MIN..=I::MAX {
            for second in I::MIN..=I::MAX {
                let name = format!("Mul: ({} * {})", first, second);
                check_mul(&name, first, second, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
            }
        }
    }

    #[test]
    fn test_u8_constant_times_constant() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_times_public() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Public, 3, 0, 26, 28);
    }

    #[test]
    fn test_u8_constant_times_private() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Private, 3, 0, 26, 28);
    }

    #[test]
    fn test_u8_public_times_constant() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Constant, 3, 0, 26, 28);
    }

    #[test]
    fn test_u8_private_times_constant() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Constant, 3, 0, 26, 28);
    }

    #[test]
    fn test_u8_public_times_public() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Public, 3, 0, 26, 28);
    }

    #[test]
    fn test_u8_public_times_private() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Private, 3, 0, 26, 28);
    }

    #[test]
    fn test_u8_private_times_public() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Public, 3, 0, 26, 28);
    }

    #[test]
    fn test_u8_private_times_private() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Private, 3, 0, 26, 28);
    }

    // Tests for i8

    #[test]
    fn test_i8_constant_times_constant() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_times_public() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Public, 40, 0, 76, 80);
    }

    #[test]
    fn test_i8_constant_times_private() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Private, 40, 0, 76, 80);
    }

    #[test]
    fn test_i8_public_times_constant() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Constant, 40, 0, 76, 80);
    }

    #[test]
    fn test_i8_private_times_constant() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Constant, 40, 0, 76, 80);
    }

    #[test]
    fn test_i8_public_times_public() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Public, 34, 0, 96, 101);
    }

    #[test]
    fn test_i8_public_times_private() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Private, 34, 0, 96, 101);
    }

    #[test]
    fn test_i8_private_times_public() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Public, 34, 0, 96, 101);
    }

    #[test]
    fn test_i8_private_times_private() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Private, 34, 0, 96, 101);
    }

    // Tests for u16

    #[test]
    fn test_u16_constant_times_constant() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_times_public() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Public, 3, 0, 50, 52);
    }

    #[test]
    fn test_u16_constant_times_private() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Private, 3, 0, 50, 52);
    }

    #[test]
    fn test_u16_public_times_constant() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Constant, 3, 0, 50, 52);
    }

    #[test]
    fn test_u16_private_times_constant() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Constant, 3, 0, 50, 52);
    }

    #[test]
    fn test_u16_public_times_public() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Public, 3, 0, 50, 52);
    }

    #[test]
    fn test_u16_public_times_private() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Private, 3, 0, 50, 52);
    }

    #[test]
    fn test_u16_private_times_public() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Public, 3, 0, 50, 52);
    }

    #[test]
    fn test_u16_private_times_private() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Private, 3, 0, 50, 52);
    }

    // Tests for i16

    #[test]
    fn test_i16_constant_times_constant() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_times_public() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Public, 72, 0, 140, 144);
    }

    #[test]
    fn test_i16_constant_times_private() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Private, 72, 0, 140, 144);
    }

    #[test]
    fn test_i16_public_times_constant() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Constant, 72, 0, 140, 144);
    }

    #[test]
    fn test_i16_private_times_constant() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Constant, 72, 0, 140, 144);
    }

    #[test]
    fn test_i16_public_times_public() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Public, 58, 0, 176, 181);
    }

    #[test]
    fn test_i16_public_times_private() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Private, 58, 0, 176, 181);
    }

    #[test]
    fn test_i16_private_times_public() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Public, 58, 0, 176, 181);
    }

    #[test]
    fn test_i16_private_times_private() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Private, 58, 0, 176, 181);
    }

    // Tests for u32

    #[test]
    fn test_u32_constant_times_constant() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_times_public() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Public, 3, 0, 98, 100);
    }

    #[test]
    fn test_u32_constant_times_private() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Private, 3, 0, 98, 100);
    }

    #[test]
    fn test_u32_public_times_constant() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Constant, 3, 0, 98, 100);
    }

    #[test]
    fn test_u32_private_times_constant() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Constant, 3, 0, 98, 100);
    }

    #[test]
    fn test_u32_public_times_public() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Public, 3, 0, 98, 100);
    }

    #[test]
    fn test_u32_public_times_private() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Private, 3, 0, 98, 100);
    }

    #[test]
    fn test_u32_private_times_public() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Public, 3, 0, 98, 100);
    }

    #[test]
    fn test_u32_private_times_private() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Private, 3, 0, 98, 100);
    }

    // Tests for i32

    #[test]
    fn test_i32_constant_times_constant() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_times_public() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Public, 136, 0, 268, 272);
    }

    #[test]
    fn test_i32_constant_times_private() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Private, 136, 0, 268, 272)
    }

    #[test]
    fn test_i32_public_times_constant() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Constant, 136, 0, 268, 272);
    }

    #[test]
    fn test_i32_private_times_constant() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Constant, 136, 0, 268, 272);
    }

    #[test]
    fn test_i32_public_times_public() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Public, 106, 0, 336, 341);
    }

    #[test]
    fn test_i32_public_times_private() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Private, 106, 0, 336, 341);
    }

    #[test]
    fn test_i32_private_times_public() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public, 106, 0, 336, 341);
    }

    #[test]
    fn test_i32_private_times_private() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Private, 106, 0, 336, 341);
    }

    // Tests for u64

    #[test]
    fn test_u64_constant_times_constant() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_times_public() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Public, 3, 0, 194, 196);
    }

    #[test]
    fn test_u64_constant_times_private() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Private, 3, 0, 194, 196);
    }

    #[test]
    fn test_u64_public_times_constant() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Constant, 3, 0, 194, 196);
    }

    #[test]
    fn test_u64_private_times_constant() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Constant, 3, 0, 194, 196);
    }

    #[test]
    fn test_u64_public_times_public() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Public, 3, 0, 194, 196);
    }

    #[test]
    fn test_u64_public_times_private() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Private, 3, 0, 194, 196);
    }

    #[test]
    fn test_u64_private_times_public() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Public, 3, 0, 194, 196);
    }

    #[test]
    fn test_u64_private_times_private() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Private, 3, 0, 194, 196);
    }

    // Tests for i64

    #[test]
    fn test_i64_constant_times_constant() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_times_public() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Public, 264, 0, 524, 528);
    }

    #[test]
    fn test_i64_constant_times_private() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Private, 264, 0, 524, 528);
    }

    #[test]
    fn test_i64_public_times_constant() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Constant, 264, 0, 524, 528);
    }

    #[test]
    fn test_i64_private_times_constant() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Constant, 264, 0, 524, 528);
    }

    #[test]
    fn test_i64_public_times_public() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Public, 202, 0, 656, 661);
    }

    #[test]
    fn test_i64_public_times_private() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Private, 202, 0, 656, 661);
    }

    #[test]
    fn test_i64_private_times_public() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Public, 202, 0, 656, 661);
    }

    #[test]
    fn test_i64_private_times_private() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Private, 202, 0, 656, 661);
    }

    // Tests for u128

    #[test]
    fn test_u128_constant_times_constant() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_times_public() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Public, 9, 0, 521, 524);
    }

    #[test]
    fn test_u128_constant_times_private() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Private, 9, 0, 521, 524);
    }

    #[test]
    fn test_u128_public_times_constant() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Constant, 9, 0, 521, 524);
    }

    #[test]
    fn test_u128_private_times_constant() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Constant, 9, 0, 521, 524);
    }

    #[test]
    fn test_u128_public_times_public() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Public, 9, 0, 521, 524);
    }

    #[test]
    fn test_u128_public_times_private() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Private, 9, 0, 521, 524);
    }

    #[test]
    fn test_u128_private_times_public() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Public, 9, 0, 521, 524);
    }

    #[test]
    fn test_u128_private_times_private() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Private, 9, 0, 521, 524);
    }

    // Tests for i128

    #[test]
    fn test_i128_constant_times_constant() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_times_public() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Public, 526, 0, 1171, 1176);
    }

    #[test]
    fn test_i128_constant_times_private() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Private, 526, 0, 1171, 1176);
    }

    #[test]
    fn test_i128_public_times_constant() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Constant, 526, 0, 1171, 1176);
    }

    #[test]
    fn test_i128_private_times_constant() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Constant, 526, 0, 1171, 1176);
    }

    #[test]
    fn test_i128_public_times_public() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Public, 400, 0, 1431, 1437);
    }

    #[test]
    fn test_i128_public_times_private() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Private, 400, 0, 1431, 1437);
    }

    #[test]
    fn test_i128_private_times_public() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Public, 400, 0, 1431, 1437);
    }

    #[test]
    fn test_i128_private_times_private() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Private, 400, 0, 1431, 1437);
    }

    // Exhaustive tests for u8.

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_times_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_times_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Public, 3, 0, 26, 28);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_times_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Private, 3, 0, 26, 28);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_times_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Constant, 3, 0, 26, 28);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_times_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Constant, 3, 0, 26, 28);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_times_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Public, 3, 0, 26, 28);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_times_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Private, 3, 0, 26, 28);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_times_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Public, 3, 0, 26, 28);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_times_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Private, 3, 0, 26, 28);
    }

    // Tests for i8

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_times_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_times_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Public, 40, 0, 76, 80);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_times_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Private, 40, 0, 76, 80);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_times_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Constant, 40, 0, 76, 80);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_times_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Constant, 40, 0, 76, 80);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_times_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Public, 34, 0, 96, 101);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_times_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Private, 34, 0, 96, 101);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_times_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Public, 34, 0, 96, 101);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_times_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Private, 34, 0, 96, 101);
    }
}
