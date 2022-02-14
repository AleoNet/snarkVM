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

impl<E: Environment, I: IntegerType, M: private::Magnitude> PowChecked<Integer<E, M>> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn pow_checked(&self, other: &Integer<E, M>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the result and return the new constant.
            // This cast is safe since `Magnitude`s can only be `u8`, `u16`, or `u32`.
            match self.eject_value().checked_pow(other.eject_value().to_u32().unwrap()) {
                Some(value) => Integer::new(Mode::Constant, value),
                None => E::halt("Integer overflow on exponentiation of two constants"),
            }
        } else {
            let mut result = Self::one();

            // TODO (@pranav) In each step, we check that we have not overflowed,
            //  yet we know that in the first step, we do not need to check and
            //  in general we do not need to check for overflow until we have found
            //  the second bit that has been set. Optimize.
            for bit in other.bits_le.iter().rev() {
                println!("Result: {:?}", result.eject_value());
                result = (&result).mul_checked(&result);
                // TODO (@pranav) We explicitly inline the implementation for mul_checked
                //  since we only want to check for overflow if the bit of the exponent is set.
                //  Dedup this code.
                let result_times_self = if I::is_signed() {
                    // This is safe since I::BITS is always greater than 0.
                    let result_msb = result.bits_le.last().unwrap();
                    let self_msb = self.bits_le.last().unwrap();

                    // Multiply the absolute value of `self` and `other` in the base field.
                    let result_absolute_value =
                        Self::ternary(result_msb, &(!&result).add_wrapped(&Self::one()), &result);
                    let self_absolute_value = Self::ternary(self_msb, &(!self).add_wrapped(&Self::one()), self);
                    let mut bits_le =
                        Self::mul_bits(&result_absolute_value.bits_le, &self_absolute_value.bits_le, true);

                    let bits_are_nonzero = |bits: &[Boolean<E>]| {
                        bits.iter().fold(Boolean::new(Mode::Constant, false), |bit, at_least_one_is_set| {
                            bit | at_least_one_is_set
                        })
                    };

                    // We need to check that the abs(a) * abs(b) did not exceed the unsigned maximum.
                    let carry_bits_nonzero = bits_are_nonzero(&bits_le[I::BITS..]);

                    let product_msb = &bits_le[I::BITS - 1];
                    let operands_same_sign = &result_msb.is_eq(self_msb);

                    // If the product should be positive, then it cannot exceed the signed maximum.
                    let positive_product_overflows = operands_same_sign & product_msb;

                    // If the product should be negative, then it cannot exceed the absolute value of the signed minimum.
                    let lower_product_bits_nonzero = &bits_are_nonzero(&bits_le[..(I::BITS - 1)]);
                    let negative_product_lt_or_eq_signed_min =
                        !product_msb | (product_msb & !lower_product_bits_nonzero);
                    let negative_product_underflows = !operands_same_sign & !negative_product_lt_or_eq_signed_min;

                    let overflow = carry_bits_nonzero | positive_product_overflows | negative_product_underflows;
                    E::assert_eq(overflow & bit, E::zero());

                    // Remove carry bits.
                    bits_le.truncate(I::BITS);

                    let value = Integer { bits_le, phantom: Default::default() };

                    // Return the product of `self` and `other` with the appropriate sign.
                    Self::ternary(operands_same_sign, &value, &(!&value).add_wrapped(&Self::one()))
                } else {
                    let mut bits_le = Self::mul_bits(&result.bits_le, &self.bits_le, true);

                    // For unsigned multiplication, check that the none of the carry bits are set.
                    let overflow = bits_le[I::BITS..]
                        .iter()
                        .fold(Boolean::new(Mode::Constant, false), |bit, at_least_one_is_set| {
                            bit | at_least_one_is_set
                        });
                    E::assert_eq(overflow & bit, E::zero());

                    // Remove carry bits.
                    bits_le.truncate(I::BITS);

                    // Return the product of `self` and `other`.
                    Integer { bits_le, phantom: Default::default() }
                };

                result = Self::ternary(&bit, &result_times_self, &result);
            }
            result
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{integers::test_utilities::*, Circuit};
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;
    use std::ops::RangeInclusive;

    // Lowered to 32, since we run (~5 * ITERATIONS) cases for most tests.
    const ITERATIONS: usize = 32;

    #[rustfmt::skip]
    fn check_pow_without_expected_numbers<I: IntegerType + std::panic::RefUnwindSafe, M: private::Magnitude + std::panic::RefUnwindSafe>(
        name: &str,
        first: I,
        second: M,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, M>::new(mode_b, second);
        let case = format!("({} ** {})", a.eject_value(), b.eject_value());
        match first.checked_pow(second.to_u32().unwrap()) {
            Some(value) => check_operation_passes_without_counts(name, &case, value, &a, &b, Integer::pow_checked),
            None => {
                match (mode_a, mode_b) {
                    (Mode::Constant, Mode::Constant) => check_operation_halts(&a, &b, Integer::pow_checked),
                    _ => check_operation_fails_without_counts(name, &case, &a, &b, Integer::pow_checked)
                }
            }
        }
    }

    #[rustfmt::skip]
    fn check_pow<I: IntegerType + std::panic::RefUnwindSafe, M: private::Magnitude + std::panic::RefUnwindSafe>(
        name: &str,
        first: I,
        second: M,
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, M>::new(mode_b, second);
        let case = format!("({} ** {})", a.eject_value(), b.eject_value());
        match first.checked_pow(second.to_u32().unwrap()) {
            Some(value) => check_operation_passes(name, &case, value, &a, &b, Integer::pow_checked, num_constants, num_public, num_private, num_constraints),
            None => {
                match (mode_a, mode_b) {
                    (Mode::Constant, Mode::Constant) => check_operation_halts(&a, &b, Integer::pow_checked),
                    _ => check_operation_fails(name, &case, &a, &b, Integer::pow_checked, num_constants, num_public, num_private, num_constraints)
                }
            }
        }
    }

    #[rustfmt::skip]
    fn run_overflow_and_corner_case_test<I: IntegerType + std::panic::RefUnwindSafe, M: private::Magnitude + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let check_pow = | name: &str, first: I, second: M | check_pow_without_expected_numbers(name, first, second, mode_a, mode_b);

        // Test operation without checking for the expected number of
        // constants, public variables, private variables, and constraints.
        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: M = UniformRand::rand(&mut thread_rng());

            let name = format!("Pow: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, second);

            let name = format!("Pow Zero: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::zero());

            let name = format!("Pow One: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::one());
        }

        // Test corner cases for exponentiation.
        check_pow("MAX ** MAX", I::MAX, M::MAX);
        check_pow("MIN ** 0", I::MIN, M::zero());
        check_pow("MAX ** 0", I::MAX, M::zero());
        check_pow("MIN ** 1", I::MIN, M::one());
        check_pow("MAX ** 1", I::MAX, M::one());
    }

    #[rustfmt::skip]
    fn run_test<I: IntegerType + std::panic::RefUnwindSafe, M: private::Magnitude + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let check_pow = | name: &str, first: I, second: M | check_pow(name, first, second, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);

        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: M = UniformRand::rand(&mut thread_rng());

            let name = format!("Pow: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, second);

            // Check that the square is computed correctly.
            let name = format!("Square: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::one() + M::one());

            // Check that the cube is computed correctly.
            let name = format!("Cube: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::one() + M::one() + M::one());

        }
    }

    #[rustfmt::skip]
    fn run_exhaustive_test_without_expected_numbers<I: IntegerType + std::panic::RefUnwindSafe, M: private::Magnitude + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode
    ) where
        RangeInclusive<I>: Iterator<Item = I>,
        RangeInclusive<M>: Iterator<Item = M>
    {
        for first in I::MIN..=I::MAX {
            for second in M::MIN..=M::MAX {
                let name = format!("Pow: ({} ** {})", first, second);
                check_pow_without_expected_numbers(&name, first, second, mode_a, mode_b);
            }
        }
    }

    #[rustfmt::skip]
    fn run_exhaustive_test<I: IntegerType + std::panic::RefUnwindSafe, M: private::Magnitude + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) where
        RangeInclusive<I>: Iterator<Item = I>,
        RangeInclusive<M>: Iterator<Item = M>
    {
        for first in I::MIN..=I::MAX {
            for second in M::MIN..=M::MAX {
                let name = format!("Pow: ({} ** {})", first, second);
                check_pow(&name, first, second, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
            }
        }
    }

    // Tests for u8, where exponent is u8

    #[test]
    fn test_u8_constant_pow_u8_constant() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_pow_u8_public() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u8_constant_pow_u8_private() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u8_public_pow_u8_constant() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u8_private_pow_u8_constant() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u8_public_pow_u8_public() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 61, 0, 462, 492);
    }

    #[test]
    fn test_u8_public_pow_u8_private() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 61, 0, 462, 492);
    }

    #[test]
    fn test_u8_private_pow_u8_public() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 61, 0, 462, 492);
    }

    #[test]
    fn test_u8_private_pow_u8_private() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 61, 0, 462, 492);
    }

    // Tests for i8, where exponent is u8

    #[test]
    fn test_i8_constant_pow_u8_constant() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_pow_u8_public() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i8_constant_pow_u8_private() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i8_public_pow_u8_constant() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i8_private_pow_u8_constant() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i8_public_pow_u8_public() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 532, 0, 1492, 1566);
    }

    #[test]
    fn test_i8_public_pow_u8_private() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 532, 0, 1492, 1566);
    }

    #[test]
    fn test_i8_private_pow_u8_public() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 532, 0, 1492, 1566);
    }

    #[test]
    fn test_i8_private_pow_u8_private() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 532, 0, 1492, 1566);
    }

    // Tests for u16, where exponent is u8

    #[test]
    fn test_u16_constant_pow_u8_constant() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_pow_u8_public() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u16_constant_pow_u8_private() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u16_public_pow_u8_constant() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u16_private_pow_u8_constant() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u16_public_pow_u8_public() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 77, 0, 886, 916);
    }

    #[test]
    fn test_u16_public_pow_u8_private() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 77, 0, 886, 916);
    }

    #[test]
    fn test_u16_private_pow_u8_public() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 77, 0, 886, 916);
    }

    #[test]
    fn test_u16_private_pow_u8_private() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 77, 0, 886, 916);
    }

    // Tests for i16, where exponent is u8

    #[test]
    fn test_i16_constant_pow_u8_constant() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_pow_u8_public() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i16_constant_pow_u8_private() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i16_public_pow_u8_constant() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i16_private_pow_u8_constant() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i16_public_pow_u8_public() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 916, 0, 2740, 2814);
    }

    #[test]
    fn test_i16_public_pow_u8_private() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 916, 0, 2740, 2814);
    }

    #[test]
    fn test_i16_private_pow_u8_public() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 916, 0, 2740, 2814);
    }

    #[test]
    fn test_i16_private_pow_u8_private() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 916, 0, 2740, 2814);
    }

    // Tests for u32, where exponent is u8

    #[test]
    fn test_u32_constant_pow_u8_constant() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_pow_u8_public() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u32_constant_pow_u8_private() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u32_public_pow_u8_constant() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u32_private_pow_u8_constant() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u32_public_pow_u8_public() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 109, 0, 1734, 1764);
    }

    #[test]
    fn test_u32_public_pow_u8_private() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 109, 0, 1734, 1764);
    }

    #[test]
    fn test_u32_private_pow_u8_public() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 109, 0, 1734, 1764);
    }

    #[test]
    fn test_u32_private_pow_u8_private() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 109, 0, 1734, 1764);
    }

    // Tests for i32, where exponent is u8

    #[test]
    fn test_i32_constant_pow_u8_constant() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_pow_u8_public() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i32_constant_pow_u8_private() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i32_public_pow_u8_constant() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i32_private_pow_u8_constant() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i32_public_pow_u8_public() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 1684, 0, 5236, 5310);
    }

    #[test]
    fn test_i32_public_pow_u8_private() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 1684, 0, 5236, 5310);
    }

    #[test]
    fn test_i32_private_pow_u8_public() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 1684, 0, 5236, 5310);
    }

    #[test]
    fn test_i32_private_pow_u8_private() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 1684, 0, 5236, 5310);
    }

    // Tests for u64, where exponent is u8

    #[test]
    fn test_u64_constant_pow_u8_constant() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_pow_u8_public() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u64_constant_pow_u8_private() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u64_public_pow_u8_constant() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u64_private_pow_u8_constant() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u64_public_pow_u8_public() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 173, 0, 3430, 3460);
    }

    #[test]
    fn test_u64_public_pow_u8_private() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 173, 0, 3430, 3460);
    }

    #[test]
    fn test_u64_private_pow_u8_public() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 173, 0, 3430, 3460);
    }

    #[test]
    fn test_u64_private_pow_u8_private() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 173, 0, 3430, 3460);
    }

    // Tests for i64, where exponent is u8

    #[test]
    fn test_i64_constant_pow_u8_constant() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_pow_u8_public() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i64_constant_pow_u8_private() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i64_public_pow_u8_constant() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i64_private_pow_u8_constant() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i64_public_pow_u8_public() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 3220, 0, 10228, 10302);
    }

    #[test]
    fn test_i64_public_pow_u8_private() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 3220, 0, 10228, 10302);
    }

    #[test]
    fn test_i64_private_pow_u8_public() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 3220, 0, 10228, 10302);
    }

    #[test]
    fn test_i64_private_pow_u8_private() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 3220, 0, 10228, 10302);
    }

    // Tests for u128, where exponent is u8

    #[test]
    fn test_u128_constant_pow_u8_constant() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_pow_u8_public() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u128_constant_pow_u8_private() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u128_public_pow_u8_constant() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u128_private_pow_u8_constant() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u128_public_pow_u8_public() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 391, 0, 8847, 8892);
    }

    #[test]
    fn test_u128_public_pow_u8_private() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 391, 0, 8847, 8892);
    }

    #[test]
    fn test_u128_private_pow_u8_public() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 391, 0, 8847, 8892);
    }

    #[test]
    fn test_u128_private_pow_u8_private() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 391, 0, 8847, 8892);
    }

    // Tests for i128, where exponent is u8

    #[test]
    fn test_i128_constant_pow_u8_constant() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_pow_u8_public() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i128_constant_pow_u8_private() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i128_public_pow_u8_constant() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i128_private_pow_u8_constant() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i128_public_pow_u8_public() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 6382, 0, 22237, 22326);
    }

    #[test]
    fn test_i128_public_pow_u8_private() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 6382, 0, 22237, 22326);
    }

    #[test]
    fn test_i128_private_pow_u8_public() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 6382, 0, 22237, 22326);
    }

    #[test]
    fn test_i128_private_pow_u8_private() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 6382, 0, 22237, 22326);
    }

    // Tests for u8, where exponent is u16

    #[test]
    fn test_u8_constant_pow_u16_constant() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_pow_u16_public() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u8_constant_pow_u16_private() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u8_public_pow_u16_constant() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u8_private_pow_u16_constant() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u8_public_pow_u16_public() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 109, 0, 950, 1012);
    }

    #[test]
    fn test_u8_public_pow_u16_private() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 109, 0, 950, 1012);
    }

    #[test]
    fn test_u8_private_pow_u16_public() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 109, 0, 950, 1012);
    }

    #[test]
    fn test_u8_private_pow_u16_private() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 109, 0, 950, 1012);
    }

    // Tests for i8, where exponent is u16

    #[test]
    fn test_i8_constant_pow_u16_constant() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_pow_u16_public() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i8_constant_pow_u16_private() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i8_public_pow_u16_constant() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i8_private_pow_u16_constant() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i8_public_pow_u16_public() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 1076, 0, 3100, 3254);
    }

    #[test]
    fn test_i8_public_pow_u16_private() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 1076, 0, 3100, 3254);
    }

    #[test]
    fn test_i8_private_pow_u16_public() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 1076, 0, 3100, 3254);
    }

    #[test]
    fn test_i8_private_pow_u16_private() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 1076, 0, 3100, 3254);
    }

    // Tests for u16, where exponent is u16

    #[test]
    fn test_u16_constant_pow_u16_constant() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_pow_u16_public() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u16_constant_pow_u16_private() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u16_public_pow_u16_constant() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u16_private_pow_u16_constant() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u16_public_pow_u16_public() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 125, 0, 1822, 1884);
    }

    #[test]
    fn test_u16_public_pow_u16_private() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 125, 0, 1822, 1884);
    }

    #[test]
    fn test_u16_private_pow_u16_public() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 125, 0, 1822, 1884);
    }

    #[test]
    fn test_u16_private_pow_u16_private() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 125, 0, 1822, 1884);
    }

    // Tests for i16, where exponent is u16

    #[test]
    fn test_i16_constant_pow_u16_constant() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_pow_u16_public() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i16_constant_pow_u16_private() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i16_public_pow_u16_constant() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i16_private_pow_u16_constant() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i16_public_pow_u16_public() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 1844, 0, 5692, 5846);
    }

    #[test]
    fn test_i16_public_pow_u16_private() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 1844, 0, 5692, 5846);
    }

    #[test]
    fn test_i16_private_pow_u16_public() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 1844, 0, 5692, 5846);
    }

    #[test]
    fn test_i16_private_pow_u16_private() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 1844, 0, 5692, 5846);
    }

    // Tests for u32, where exponent is u16

    #[test]
    fn test_u32_constant_pow_u16_constant() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_pow_u16_public() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u32_constant_pow_u16_private() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u32_public_pow_u16_constant() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u32_private_pow_u16_constant() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u32_public_pow_u16_public() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 157, 0, 3566, 3628);
    }

    #[test]
    fn test_u32_public_pow_u16_private() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 157, 0, 3566, 3628);
    }

    #[test]
    fn test_u32_private_pow_u16_public() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 157, 0, 3566, 3628);
    }

    #[test]
    fn test_u32_private_pow_u16_private() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 157, 0, 3566, 3628);
    }

    // Tests for i32, where exponent is u16

    #[test]
    fn test_i32_constant_pow_u16_constant() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_pow_u16_public() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i32_constant_pow_u16_private() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i32_public_pow_u16_constant() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i32_private_pow_u16_constant() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i32_public_pow_u16_public() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 3380, 0, 10876, 11030);
    }

    #[test]
    fn test_i32_public_pow_u16_private() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 3380, 0, 10876, 11030);
    }

    #[test]
    fn test_i32_private_pow_u16_public() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 3380, 0, 10876, 11030);
    }

    #[test]
    fn test_i32_private_pow_u16_private() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 3380, 0, 10876, 11030);
    }

    // Tests for u64, where exponent is u16

    #[test]
    fn test_u64_constant_pow_u16_constant() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_pow_u16_public() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u64_constant_pow_u16_private() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u64_public_pow_u16_constant() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u64_private_pow_u16_constant() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u64_public_pow_u16_public() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 221, 0, 7054, 7116);
    }

    #[test]
    fn test_u64_public_pow_u16_private() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 221, 0, 7054, 7116);
    }

    #[test]
    fn test_u64_private_pow_u16_public() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 221, 0, 7054, 7116);
    }

    #[test]
    fn test_u64_private_pow_u16_private() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 221, 0, 7054, 7116);
    }

    // Tests for i64, where exponent is u16

    #[test]
    fn test_i64_constant_pow_u16_constant() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_pow_u16_public() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i64_constant_pow_u16_private() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i64_public_pow_u16_constant() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i64_private_pow_u16_constant() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i64_public_pow_u16_public() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 6452, 0, 21244, 21398);
    }

    #[test]
    fn test_i64_public_pow_u16_private() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 6452, 0, 21244, 21398);
    }

    #[test]
    fn test_i64_private_pow_u16_public() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 6452, 0, 21244, 21398);
    }

    #[test]
    fn test_i64_private_pow_u16_private() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 6452, 0, 21244, 21398);
    }

    // Tests for u128, where exponent is u16

    #[test]
    fn test_u128_constant_pow_u16_constant() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_pow_u16_public() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u128_constant_pow_u16_private() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u128_public_pow_u16_constant() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u128_private_pow_u16_constant() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u128_public_pow_u16_public() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 535, 0, 18215, 18308);
    }

    #[test]
    fn test_u128_public_pow_u16_private() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 535, 0, 18215, 18308);
    }

    #[test]
    fn test_u128_private_pow_u16_public() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 535, 0, 18215, 18308);
    }

    #[test]
    fn test_u128_private_pow_u16_private() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 535, 0, 18215, 18308);
    }

    // Tests for i128, where exponent is u16

    #[test]
    fn test_i128_constant_pow_u16_constant() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_pow_u16_public() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i128_constant_pow_u16_private() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i128_public_pow_u16_constant() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i128_private_pow_u16_constant() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i128_public_pow_u16_public() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 12782, 0, 46165, 46350);
    }

    #[test]
    fn test_i128_public_pow_u16_private() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 12782, 0, 46165, 46350);
    }

    #[test]
    fn test_i128_private_pow_u16_public() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 12782, 0, 46165, 46350);
    }

    #[test]
    fn test_i128_private_pow_u16_private() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 12782, 0, 46165, 46350);
    }

    // Tests for u8, where exponent is u32

    #[test]
    fn test_u8_constant_pow_u32_constant() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_pow_u32_public() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u8_constant_pow_u32_private() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u8_public_pow_u32_constant() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u8_private_pow_u32_constant() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u8_public_pow_u32_public() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 205, 0, 1926, 2052);
    }

    #[test]
    fn test_u8_public_pow_u32_private() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 205, 0, 1926, 2052);
    }

    #[test]
    fn test_u8_private_pow_u32_public() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 205, 0, 1926, 2052);
    }

    #[test]
    fn test_u8_private_pow_u32_private() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 205, 0, 1926, 2052);
    }

    // Tests for i8, where exponent is u32

    #[test]
    fn test_i8_constant_pow_u32_constant() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_pow_u32_public() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i8_constant_pow_u32_private() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i8_public_pow_u32_constant() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i8_private_pow_u32_constant() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i8_public_pow_u32_public() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 2164, 0, 6316, 6630);
    }

    #[test]
    fn test_i8_public_pow_u32_private() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 2164, 0, 6316, 6630);
    }

    #[test]
    fn test_i8_private_pow_u32_public() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 2164, 0, 6316, 6630);
    }

    #[test]
    fn test_i8_private_pow_u32_private() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 2164, 0, 6316, 6630);
    }

    // Tests for u16, where exponent is u32

    #[test]
    fn test_u16_constant_pow_u32_constant() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_pow_u32_public() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u16_constant_pow_u32_private() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u16_public_pow_u32_constant() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u16_private_pow_u32_constant() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u16_public_pow_u32_public() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 221, 0, 3694, 3820);
    }

    #[test]
    fn test_u16_public_pow_u32_private() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 221, 0, 3694, 3820);
    }

    #[test]
    fn test_u16_private_pow_u32_public() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 221, 0, 3694, 3820);
    }

    #[test]
    fn test_u16_private_pow_u32_private() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 221, 0, 3694, 3820);
    }

    // Tests for i16, where exponent is u32

    #[test]
    fn test_i16_constant_pow_u32_constant() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_pow_u32_public() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i16_constant_pow_u32_private() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i16_public_pow_u32_constant() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i16_private_pow_u32_constant() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i16_public_pow_u32_public() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 3700, 0, 11596, 11910);
    }

    #[test]
    fn test_i16_public_pow_u32_private() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 3700, 0, 11596, 11910);
    }

    #[test]
    fn test_i16_private_pow_u32_public() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 3700, 0, 11596, 11910);
    }

    #[test]
    fn test_i16_private_pow_u32_private() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 3700, 0, 11596, 11910);
    }

    // Tests for u32, where exponent is u32

    #[test]
    fn test_u32_constant_pow_u32_constant() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_pow_u32_public() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u32_constant_pow_u32_private() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u32_public_pow_u32_constant() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u32_private_pow_u32_constant() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u32_public_pow_u32_public() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 253, 0, 7230, 7356);
    }

    #[test]
    fn test_u32_public_pow_u32_private() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 253, 0, 7230, 7356);
    }

    #[test]
    fn test_u32_private_pow_u32_public() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 253, 0, 7230, 7356);
    }

    #[test]
    fn test_u32_private_pow_u32_private() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 253, 0, 7230, 7356);
    }

    // Tests for i32, where exponent is u32

    #[test]
    fn test_i32_constant_pow_u32_constant() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_pow_u32_public() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i32_constant_pow_u32_private() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i32_public_pow_u32_constant() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i32_private_pow_u32_constant() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i32_public_pow_u32_public() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 6772, 0, 22156, 22470);
    }

    #[test]
    fn test_i32_public_pow_u32_private() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 6772, 0, 22156, 22470);
    }

    #[test]
    fn test_i32_private_pow_u32_public() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 6772, 0, 22156, 22470);
    }

    #[test]
    fn test_i32_private_pow_u32_private() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 6772, 0, 22156, 22470);
    }

    // Tests for u64, where exponent is u32

    #[test]
    fn test_u64_constant_pow_u32_constant() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_pow_u32_public() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u64_constant_pow_u32_private() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u64_public_pow_u32_constant() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u64_private_pow_u32_constant() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u64_public_pow_u32_public() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 317, 0, 14302, 14428);
    }

    #[test]
    fn test_u64_public_pow_u32_private() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 317, 0, 14302, 14428);
    }

    #[test]
    fn test_u64_private_pow_u32_public() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 317, 0, 14302, 14428);
    }

    #[test]
    fn test_u64_private_pow_u32_private() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 317, 0, 14302, 14428);
    }

    // Tests for i64, where exponent is u32

    #[test]
    fn test_i64_constant_pow_u32_constant() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_pow_u32_public() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i64_constant_pow_u32_private() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i64_public_pow_u32_constant() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i64_private_pow_u32_constant() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i64_public_pow_u32_public() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 12916, 0, 43276, 43590);
    }

    #[test]
    fn test_i64_public_pow_u32_private() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 12916, 0, 43276, 43590);
    }

    #[test]
    fn test_i64_private_pow_u32_public() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 12916, 0, 43276, 43590);
    }

    #[test]
    fn test_i64_private_pow_u32_private() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 12916, 0, 43276, 43590);
    }

    // Tests for u128, where exponent is u32

    #[test]
    fn test_u128_constant_pow_u32_constant() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_pow_u32_public() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u128_constant_pow_u32_private() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u128_public_pow_u32_constant() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u128_private_pow_u32_constant() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u128_public_pow_u32_public() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 823, 0, 36951, 37140);
    }

    #[test]
    fn test_u128_public_pow_u32_private() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 823, 0, 36951, 37140);
    }

    #[test]
    fn test_u128_private_pow_u32_public() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 823, 0, 36951, 37140);
    }

    #[test]
    fn test_u128_private_pow_u32_private() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 823, 0, 36951, 37140);
    }

    // Tests for i128, where exponent is u32

    #[test]
    fn test_i128_constant_pow_u32_constant() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_pow_u32_public() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i128_constant_pow_u32_private() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i128_public_pow_u32_constant() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i128_private_pow_u32_constant() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i128_public_pow_u32_public() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Public);
        run_test::<I, M>(Mode::Public, Mode::Public, 25582, 0, 94021, 94398);
    }

    #[test]
    fn test_i128_public_pow_u32_private() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 25582, 0, 94021, 94398);
    }

    #[test]
    fn test_i128_private_pow_u32_public() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 25582, 0, 94021, 94398);
    }

    #[test]
    fn test_i128_private_pow_u32_private() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 25582, 0, 94021, 94398);
    }

    // Exhaustive tests for u8, where exponent is u8

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_pow_u8_constant() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_pow_u8_public() {
        type I = u8;
        type M = u8;
        run_exhaustive_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_pow_u8_private() {
        type I = u8;
        type M = u8;
        run_exhaustive_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_pow_u8_constant() {
        type I = u8;
        type M = u8;
        run_exhaustive_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_pow_u8_constant() {
        type I = u8;
        type M = u8;
        run_exhaustive_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_pow_u8_public() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Public, 61, 0, 462, 492);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_pow_u8_private() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Private, 61, 0, 462, 492);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_pow_u8_public() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Public, 61, 0, 462, 492);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_pow_u8_private() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Private, 61, 0, 462, 492);
    }

    // Exhaustive tests for i8, where exponent is u8

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_pow_u8_constant() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_pow_u8_public() {
        type I = i8;
        type M = u8;
        run_exhaustive_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_pow_u8_private() {
        type I = i8;
        type M = u8;
        run_exhaustive_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_pow_u8_constant() {
        type I = i8;
        type M = u8;
        run_exhaustive_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_pow_u8_constant() {
        type I = i8;
        type M = u8;
        run_exhaustive_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_pow_u8_public() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Public, 532, 0, 1492, 1566);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_pow_u8_private() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Private, 532, 0, 1492, 1566);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_pow_u8_public() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Public, 532, 0, 1492, 1566);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_pow_u8_private() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Private, 532, 0, 1492, 1566);
    }
}
