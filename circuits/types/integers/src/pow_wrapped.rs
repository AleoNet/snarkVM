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

use super::*;

impl<E: Environment, I: IntegerType, M: Magnitude> PowWrapped<Integer<E, M>> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn pow_wrapped(&self, other: &Integer<E, M>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the result and return the new constant.
            // This cast is safe since Magnitude other can only be `u8`, `u16`, or `u32`.
            witness!(|self, other| self.wrapping_pow(&other.to_u32().unwrap()))
        } else {
            let mut result = Self::one();
            for bit in other.bits_le.iter().rev() {
                result = (&result).mul_wrapped(&result);
                result = Self::ternary(bit, &result.mul_wrapped(self), &result);
            }
            result
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};
    use test_utilities::*;

    use std::{ops::RangeInclusive, panic::RefUnwindSafe};

    // Lowered to 4; we run (~6 * ITERATIONS) cases for most tests.
    const ITERATIONS: usize = 4;

    #[rustfmt::skip]
    fn check_pow<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(
        name: &str,
        first: I,
        second: M,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, M>::new(mode_b, second);
        let case = format!("({} ** {})", a.eject_value(), b.eject_value());
        let expected = first.wrapping_pow(&second.to_u32().unwrap());
        check_operation_passes_without_counts(name, &case, expected, &a, &b, Integer::pow_wrapped);
    }

    fn run_overflow_and_corner_case_test<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let rng = &mut test_rng();

        // Test operation without checking for the expected number of
        // constants, public variables, private variables, and constraints.
        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(rng);
            let second: M = UniformRand::rand(rng);

            let name = format!("Pow: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, second, mode_a, mode_b);

            let name = format!("Pow Zero: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::zero(), mode_a, mode_b);

            let name = format!("Pow One: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::one(), mode_a, mode_b);
        }

        // Test corner cases for exponentiation.
        check_pow("MAX ** MAX", I::MAX, M::MAX, mode_a, mode_b);
        check_pow("MIN ** 0", I::MIN, M::zero(), mode_a, mode_b);
        check_pow("MAX ** 0", I::MAX, M::zero(), mode_a, mode_b);
        check_pow("MIN ** 1", I::MIN, M::one(), mode_a, mode_b);
        check_pow("MAX ** 1", I::MAX, M::one(), mode_a, mode_b);
    }

    fn run_test<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(mode_a: Mode, mode_b: Mode) {
        let rng = &mut test_rng();

        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(rng);
            let second: M = UniformRand::rand(rng);

            let name = format!("Pow: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, second, mode_a, mode_b);

            // Check that the square is computed correctly.
            let name = format!("Square: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::one() + M::one(), mode_a, mode_b);

            // Check that the cube is computed correctly.
            let name = format!("Cube: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::one() + M::one() + M::one(), mode_a, mode_b);
        }
    }

    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(mode_a: Mode, mode_b: Mode)
    where
        RangeInclusive<I>: Iterator<Item = I>,
        RangeInclusive<M>: Iterator<Item = M>,
    {
        for first in I::MIN..=I::MAX {
            for second in M::MIN..=M::MAX {
                let name = format!("Pow: ({} ** {})", first, second);
                check_pow(&name, first, second, mode_a, mode_b);
            }
        }
    }

    // Tests for u8, where exponent is u8

    #[test]
    fn test_u8_constant_pow_u8_constant() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u8_public_pow_u8_private() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u8_private_pow_u8_public() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u8_private_pow_u8_private() {
        type I = u8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for i8, where exponent is u8

    #[test]
    fn test_i8_constant_pow_u8_constant() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i8_public_pow_u8_private() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i8_private_pow_u8_public() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i8_private_pow_u8_private() {
        type I = i8;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for u16, where exponent is u8

    #[test]
    fn test_u16_constant_pow_u8_constant() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u16_public_pow_u8_private() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u16_private_pow_u8_public() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u16_private_pow_u8_private() {
        type I = u16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for i16, where exponent is u8

    #[test]
    fn test_i16_constant_pow_u8_constant() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i16_public_pow_u8_private() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i16_private_pow_u8_public() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i16_private_pow_u8_private() {
        type I = i16;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for u32, where exponent is u8

    #[test]
    fn test_u32_constant_pow_u8_constant() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u32_public_pow_u8_private() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u32_private_pow_u8_public() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u32_private_pow_u8_private() {
        type I = u32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for i32, where exponent is u8

    #[test]
    fn test_i32_constant_pow_u8_constant() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i32_public_pow_u8_private() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i32_private_pow_u8_public() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i32_private_pow_u8_private() {
        type I = i32;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for u64, where exponent is u8

    #[test]
    fn test_u64_constant_pow_u8_constant() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u64_public_pow_u8_private() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u64_private_pow_u8_public() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u64_private_pow_u8_private() {
        type I = u64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for i64, where exponent is u8

    #[test]
    fn test_i64_constant_pow_u8_constant() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i64_public_pow_u8_private() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i64_private_pow_u8_public() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i64_private_pow_u8_private() {
        type I = i64;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for u128, where exponent is u8

    #[test]
    fn test_u128_constant_pow_u8_constant() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u128_public_pow_u8_private() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u128_private_pow_u8_public() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u128_private_pow_u8_private() {
        type I = u128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for i128, where exponent is u8

    #[test]
    fn test_i128_constant_pow_u8_constant() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i128_public_pow_u8_private() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i128_private_pow_u8_public() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i128_private_pow_u8_private() {
        type I = i128;
        type M = u8;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for u8, where exponent is u16

    #[test]
    fn test_u8_constant_pow_u16_constant() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u8_public_pow_u16_private() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u8_private_pow_u16_public() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u8_private_pow_u16_private() {
        type I = u8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for i8, where exponent is u16

    #[test]
    fn test_i8_constant_pow_u16_constant() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i8_public_pow_u16_private() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i8_private_pow_u16_public() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i8_private_pow_u16_private() {
        type I = i8;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for u16, where exponent is u16

    #[test]
    fn test_u16_constant_pow_u16_constant() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u16_public_pow_u16_private() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u16_private_pow_u16_public() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u16_private_pow_u16_private() {
        type I = u16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for i16, where exponent is u16

    #[test]
    fn test_i16_constant_pow_u16_constant() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i16_public_pow_u16_private() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i16_private_pow_u16_public() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i16_private_pow_u16_private() {
        type I = i16;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for u32, where exponent is u16

    #[test]
    fn test_u32_constant_pow_u16_constant() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u32_public_pow_u16_private() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u32_private_pow_u16_public() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u32_private_pow_u16_private() {
        type I = u32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for i32, where exponent is u16

    #[test]
    fn test_i32_constant_pow_u16_constant() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i32_public_pow_u16_private() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i32_private_pow_u16_public() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i32_private_pow_u16_private() {
        type I = i32;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for u64, where exponent is u16

    #[test]
    fn test_u64_constant_pow_u16_constant() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u64_public_pow_u16_private() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u64_private_pow_u16_public() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u64_private_pow_u16_private() {
        type I = u64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for i64, where exponent is u16

    #[test]
    fn test_i64_constant_pow_u16_constant() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i64_public_pow_u16_private() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i64_private_pow_u16_public() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i64_private_pow_u16_private() {
        type I = i64;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for u128, where exponent is u16

    #[test]
    fn test_u128_constant_pow_u16_constant() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u128_public_pow_u16_private() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u128_private_pow_u16_public() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u128_private_pow_u16_private() {
        type I = u128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for i128, where exponent is u16

    #[test]
    fn test_i128_constant_pow_u16_constant() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i128_public_pow_u16_private() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i128_private_pow_u16_public() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i128_private_pow_u16_private() {
        type I = i128;
        type M = u16;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for u8, where exponent is u32

    #[test]
    fn test_u8_constant_pow_u32_constant() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u8_public_pow_u32_private() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u8_private_pow_u32_public() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u8_private_pow_u32_private() {
        type I = u8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for i8, where exponent is u32

    #[test]
    fn test_i8_constant_pow_u32_constant() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i8_public_pow_u32_private() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i8_private_pow_u32_public() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i8_private_pow_u32_private() {
        type I = i8;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for u16, where exponent is u32

    #[test]
    fn test_u16_constant_pow_u32_constant() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u16_public_pow_u32_private() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u16_private_pow_u32_public() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u16_private_pow_u32_private() {
        type I = u16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for i16, where exponent is u32

    #[test]
    fn test_i16_constant_pow_u32_constant() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i16_public_pow_u32_private() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i16_private_pow_u32_public() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i16_private_pow_u32_private() {
        type I = i16;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for u32, where exponent is u32

    #[test]
    fn test_u32_constant_pow_u32_constant() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u32_public_pow_u32_private() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u32_private_pow_u32_public() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u32_private_pow_u32_private() {
        type I = u32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for i32, where exponent is u32

    #[test]
    fn test_i32_constant_pow_u32_constant() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i32_public_pow_u32_private() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i32_private_pow_u32_public() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i32_private_pow_u32_private() {
        type I = i32;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for u64, where exponent is u32

    #[test]
    fn test_u64_constant_pow_u32_constant() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u64_public_pow_u32_private() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u64_private_pow_u32_public() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u64_private_pow_u32_private() {
        type I = u64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for i64, where exponent is u32

    #[test]
    fn test_i64_constant_pow_u32_constant() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i64_public_pow_u32_private() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i64_private_pow_u32_public() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i64_private_pow_u32_private() {
        type I = i64;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for u128, where exponent is u32

    #[test]
    fn test_u128_constant_pow_u32_constant() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u128_public_pow_u32_private() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u128_private_pow_u32_public() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u128_private_pow_u32_private() {
        type I = u128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Tests for i128, where exponent is u32

    #[test]
    fn test_i128_constant_pow_u32_constant() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Constant, Mode::Constant);
        run_test::<I, M>(Mode::Constant, Mode::Constant);
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
        run_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i128_public_pow_u32_private() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Public, Mode::Private);
        run_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i128_private_pow_u32_public() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Public);
        run_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i128_private_pow_u32_private() {
        type I = i128;
        type M = u32;
        run_overflow_and_corner_case_test::<I, M>(Mode::Private, Mode::Private);
        run_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Exhaustive tests for u8, where exponent is u8

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_pow_u8_constant() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Constant, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_pow_u8_public() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_pow_u8_private() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_pow_u8_constant() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_pow_u8_constant() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_pow_u8_public() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_pow_u8_private() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_pow_u8_public() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_pow_u8_private() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Private);
    }

    // Exhaustive tests for i8, where exponent is u8

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_pow_u8_constant() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Constant, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_pow_u8_public() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Constant, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_pow_u8_private() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_pow_u8_constant() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_pow_u8_constant() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_pow_u8_public() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Public);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_pow_u8_private() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Private);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_pow_u8_public() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Public);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_pow_u8_private() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Private);
    }
}
