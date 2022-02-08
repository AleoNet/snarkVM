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

impl<E: Environment, I: IntegerType, M: private::Magnitude> PowWrapped<Integer<E, M>> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn pow_wrapped(&self, other: &Integer<E, M>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the result and return the new constant.
            // This cast is safe since Magnitude other can only be `u8`, `u16`, or `u32`.
            Integer::new(Mode::Constant, self.eject_value().wrapping_pow(other.eject_value().to_u32().unwrap()))
        } else {
            let mut result = Self::one();
            for bit in other.bits_le.iter().rev() {
                result = (&result).mul_wrapped(&result);
                result = Self::ternary(bit, &result.mul_wrapped(&self), &result);
            }
            result
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;
    use test_utilities::*;

    use num_traits::checked_pow;
    use rand::thread_rng;
    use std::ops::Range;

    // Lowered to 32, since we run (~6 * ITERATIONS) cases for most tests.
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
        let expected = first.wrapping_pow(second.to_u32().unwrap());
        check_binary_operation_passes_without_expected_numbers(name, &case, expected, &a, &b, Integer::pow_checked);
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
        let expected = first.wrapping_pow(second.to_u32().unwrap());
        check_binary_operation_passes(name, &case, expected, &a, &b, Integer::pow_checked, num_constants, num_public, num_private, num_constraints);
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
        Range<I>: Iterator<Item = I>,
        Range<M>: Iterator<Item = M>
    {
        for first in I::MIN..I::MAX {
            for second in M::MIN..M::MAX {
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
        Range<I>: Iterator<Item = I>,
        Range<M>: Iterator<Item = M>
    {
        for first in I::MIN..I::MAX {
            for second in M::MIN..M::MAX {
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
        run_test::<I, M>(Mode::Public, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    fn test_u8_public_pow_u8_private() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 46, 0, 349, 364);
    }

    #[test]
    fn test_u8_private_pow_u8_public() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    fn test_u8_private_pow_u8_private() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 46, 0, 349, 364);
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
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    fn test_i8_public_pow_u8_private() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 46, 0, 349, 364);
    }

    #[test]
    fn test_i8_private_pow_u8_public() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    fn test_i8_private_pow_u8_private() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 46, 0, 349, 364);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 62, 0, 653, 668);
    }

    #[test]
    fn test_u16_public_pow_u8_private() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 62, 0, 653, 668);
    }

    #[test]
    fn test_u16_private_pow_u8_public() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 62, 0, 653, 668);
    }

    #[test]
    fn test_u16_private_pow_u8_private() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 62, 0, 653, 668);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 62, 0, 653, 668);
    }

    #[test]
    fn test_i16_public_pow_u8_private() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 62, 0, 653, 668);
    }

    #[test]
    fn test_i16_private_pow_u8_public() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 62, 0, 653, 668);
    }

    #[test]
    fn test_i16_private_pow_u8_private() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 62, 0, 653, 668);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_u32_public_pow_u8_private() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_u32_private_pow_u8_public() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_u32_private_pow_u8_private() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 94, 0, 1261, 1276);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_i32_public_pow_u8_private() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_i32_private_pow_u8_public() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_i32_private_pow_u8_private() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 94, 0, 1261, 1276);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_u64_public_pow_u8_private() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_u64_private_pow_u8_public() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_u64_private_pow_u8_private() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 158, 0, 2477, 2492);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_i64_public_pow_u8_private() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_i64_private_pow_u8_public() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_i64_private_pow_u8_private() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 158, 0, 2477, 2492);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_u128_public_pow_u8_private() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_u128_private_pow_u8_public() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_u128_private_pow_u8_private() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 376, 0, 4024, 4039);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_i128_public_pow_u8_private() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_i128_private_pow_u8_public() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_i128_private_pow_u8_private() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 376, 0, 4024, 4039);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 78, 0, 717, 748);
    }

    #[test]
    fn test_u8_public_pow_u16_private() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 78, 0, 717, 748);
    }

    #[test]
    fn test_u8_private_pow_u16_public() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 78, 0, 717, 748);
    }

    #[test]
    fn test_u8_private_pow_u16_private() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 78, 0, 717, 748);
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
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 78, 0, 717, 748);
    }

    #[test]
    fn test_i8_public_pow_u16_private() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 78, 0, 717, 748);
    }

    #[test]
    fn test_i8_private_pow_u16_public() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 78, 0, 717, 748);
    }

    #[test]
    fn test_i8_private_pow_u16_private() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 78, 0, 717, 748);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_u16_public_pow_u16_private() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_u16_private_pow_u16_public() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_u16_private_pow_u16_private() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 94, 0, 1341, 1372);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_i16_public_pow_u16_private() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_i16_private_pow_u16_public() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_i16_private_pow_u16_private() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 94, 0, 1341, 1372);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_u32_public_pow_u16_private() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_u32_private_pow_u16_public() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_u32_private_pow_u16_private() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 126, 0, 2589, 2620);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_i32_public_pow_u16_private() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_i32_private_pow_u16_public() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_i32_private_pow_u16_private() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 126, 0, 2589, 2620);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_u64_public_pow_u16_private() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_u64_private_pow_u16_public() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_u64_private_pow_u16_private() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 190, 0, 5085, 5116);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_i64_public_pow_u16_private() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_i64_private_pow_u16_public() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_i64_private_pow_u16_private() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 190, 0, 5085, 5116);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_u128_public_pow_u16_private() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_u128_private_pow_u16_public() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_u128_private_pow_u16_private() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 504, 0, 8248, 8279);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_i128_public_pow_u16_private() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_i128_private_pow_u16_public() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_i128_private_pow_u16_private() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 504, 0, 8248, 8279);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_u8_public_pow_u32_private() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_u8_private_pow_u32_public() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_u8_private_pow_u32_private() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 142, 0, 1453, 1516);
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
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_i8_public_pow_u32_private() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_i8_private_pow_u32_public() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_i8_private_pow_u32_private() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 142, 0, 1453, 1516);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_u16_public_pow_u32_private() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_u16_private_pow_u32_public() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_u16_private_pow_u32_private() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 158, 0, 2717, 2780);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_i16_public_pow_u32_private() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_i16_private_pow_u32_public() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_i16_private_pow_u32_private() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 158, 0, 2717, 2780);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_u32_public_pow_u32_private() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_u32_private_pow_u32_public() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_u32_private_pow_u32_private() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 190, 0, 5245, 5308);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_i32_public_pow_u32_private() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_i32_private_pow_u32_public() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_i32_private_pow_u32_private() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 190, 0, 5245, 5308);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_u64_public_pow_u32_private() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_u64_private_pow_u32_public() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_u64_private_pow_u32_private() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 254, 0, 10301, 10364);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_i64_public_pow_u32_private() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_i64_private_pow_u32_public() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_i64_private_pow_u32_private() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 254, 0, 10301, 10364);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_u128_public_pow_u32_private() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_u128_private_pow_u32_public() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_u128_private_pow_u32_private() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 760, 0, 16696, 16759);
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
        run_test::<I, M>(Mode::Public, Mode::Public, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_i128_public_pow_u32_private() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_i128_private_pow_u32_public() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_i128_private_pow_u32_private() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private, 760, 0, 16696, 16759);
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
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_pow_u8_private() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Private, 46, 0, 349, 364);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_pow_u8_public() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_pow_u8_private() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Private, 46, 0, 349, 364);
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
        run_exhaustive_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Constant);
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
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_pow_u8_private() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Private, 46, 0, 349, 364);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_pow_u8_public() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_pow_u8_private() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Private, 46, 0, 349, 364);
    }
}
