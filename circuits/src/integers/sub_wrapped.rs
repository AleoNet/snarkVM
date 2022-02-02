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

impl<E: Environment, I: IntegerType> SubWrapped<Self> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn sub_wrapped(&self, other: &Integer<E, I>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the difference and return the new constant.
            Integer::new(Mode::Constant, self.eject_value().wrapping_sub(&other.eject_value()))
        } else {
            // Instead of subtracting the bits of `self` and `other` directly, the integers are
            // converted into a field elements, and subtracted, before being converted back to integers.
            // Note: This is safe as the field is larger than the maximum integer type supported.
            let minuend = BaseField::from_bits_le(Mode::Private, &self.bits_le);
            let subtrahend =
                BaseField::from_bits_le(Mode::Private, &other.bits_le.iter().map(|b| !b).collect::<Vec<_>>());
            let difference = minuend + &subtrahend + BaseField::one();

            // Extract the integer bits from the field element, with a carry bit.
            let mut bits_le = difference.to_lower_bits_le(I::BITS + 1);
            // Drop the carry bit as the operation is wrapped subtraction.
            bits_le.pop();

            // Return the difference of `self` and `other`.
            Integer { bits_le, phantom: Default::default() }
        }
    }
}

#[rustfmt::skip]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 128;

    fn check_sub_wrapped<I: IntegerType, IC: IntegerTrait<I>>(
        name: &str,
        expected: I,
        a: &IC,
        b: &IC,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, || {
            let case = format!("({} - {})", a.eject_value(), b.eject_value());

            let candidate = a.sub_wrapped(b);
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := {}",
                expected,
                candidate.eject_value(),
                case
            );

            assert_eq!(num_constants, Circuit::num_constants_in_scope(), "{} (num_constants)", case);
            assert_eq!(num_public, Circuit::num_public_in_scope(), "{} (num_public)", case);
            assert_eq!(num_private, Circuit::num_private_in_scope(), "{} (num_private)", case);
            assert_eq!(num_constraints, Circuit::num_constraints_in_scope(), "{} (num_constraints)", case);
            assert!(Circuit::is_satisfied(), "{} (is_satisfied)", case);
        });
        Circuit::reset()
    }

    fn check_underflow<I: IntegerType>(
        first: I,
        second: I,
        expected: I,
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::new(mode_b, second);

        let name = format!("Sub: {} - {} ({})", first, second, expected);
        check_sub_wrapped::<I, Integer<Circuit, I>>(&name, expected, &a, &b, num_constants, num_public, num_private, num_constraints);
    }

    fn run_test<I: IntegerType>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: I = UniformRand::rand(&mut thread_rng());
            let expected = first.wrapping_sub(&second);

            let a = Integer::<Circuit, I>::new(mode_a, first);
            let b = Integer::new(mode_b, second);

            let name = format!("Sub: a - b {}", i);
            check_sub_wrapped::<I, Integer<Circuit, I>>(&name, expected, &a, &b, num_constants, num_public, num_private, num_constraints);
        }

        match I::is_signed() {
            true => {
                // Overflow
                check_underflow::<I>(I::MAX, I::zero() - I::one(), I::MIN, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);

                // Underflow
                check_underflow::<I>(I::MIN, I::one(), I::MAX, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
            },
            false => {
                // Overflow
                check_underflow::<I>(I::MIN, I::one(), I::MAX, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
            }
        }
    }

    #[test]
    fn test_u8_constant_minus_constant() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_minus_public() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 11, 12);
    }

    #[test]
    fn test_u8_constant_minus_private() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 11, 12);
    }

    #[test]
    fn test_u8_public_minus_constant() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 11, 12);
    }

    #[test]
    fn test_u8_private_minus_constant() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 11, 12);
    }

    #[test]
    fn test_u8_public_minus_public() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 11, 12);
    }

    #[test]
    fn test_u8_public_minus_private() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 11, 12);
    }

    #[test]
    fn test_u8_private_minus_public() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 11, 12);
    }

    #[test]
    fn test_u8_private_minus_private() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 11, 12);
    }

    // Tests for i8

    #[test]
    fn test_i8_constant_minus_constant() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_minus_public() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 11, 12);
    }

    #[test]
    fn test_i8_constant_minus_private() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 11, 12);
    }

    #[test]
    fn test_i8_public_minus_constant() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 11, 12);
    }

    #[test]
    fn test_i8_private_minus_constant() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 11, 12);
    }

    #[test]
    fn test_i8_public_minus_public() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 11, 12);
    }

    #[test]
    fn test_i8_public_minus_private() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 11, 12);
    }

    #[test]
    fn test_i8_private_minus_public() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 11, 12);
    }

    #[test]
    fn test_i8_private_minus_private() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 11, 12);
    }

    // Tests for u16

    #[test]
    fn test_u16_constant_minus_constant() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_minus_public() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 19, 20);
    }

    #[test]
    fn test_u16_constant_minus_private() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 19, 20);
    }

    #[test]
    fn test_u16_public_minus_constant() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 19, 20);
    }

    #[test]
    fn test_u16_private_minus_constant() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 19, 20);
    }

    #[test]
    fn test_u16_public_minus_public() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 19, 20);
    }

    #[test]
    fn test_u16_public_minus_private() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 19, 20);
    }

    #[test]
    fn test_u16_private_minus_public() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 19, 20);
    }

    #[test]
    fn test_u16_private_minus_private() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 19, 20);
    }

    // Tests for i16

    #[test]
    fn test_i16_constant_minus_constant() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_minus_public() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 19, 20);
    }

    #[test]
    fn test_i16_constant_minus_private() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 19, 20);
    }

    #[test]
    fn test_i16_public_minus_constant() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 19, 20);
    }

    #[test]
    fn test_i16_private_minus_constant() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 19, 20);
    }

    #[test]
    fn test_i16_public_minus_public() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 19, 20);
    }

    #[test]
    fn test_i16_public_minus_private() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 19, 20);
    }

    #[test]
    fn test_i16_private_minus_public() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 19, 20);
    }

    #[test]
    fn test_i16_private_minus_private() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 19, 20);
    }

    // Tests for u32

    #[test]
    fn test_u32_constant_minus_constant() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_minus_public() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 35, 36);
    }

    #[test]
    fn test_u32_constant_minus_private() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 35, 36);
    }

    #[test]
    fn test_u32_public_minus_constant() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 35, 36);
    }

    #[test]
    fn test_u32_private_minus_constant() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 35, 36);
    }

    #[test]
    fn test_u32_public_minus_public() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 35, 36);
    }

    #[test]
    fn test_u32_public_minus_private() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 35, 36);
    }

    #[test]
    fn test_u32_private_minus_public() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 35, 36);
    }

    #[test]
    fn test_u32_private_minus_private() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 35, 36);
    }

    // Tests for i32

    #[test]
    fn test_i32_constant_minus_constant() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_minus_public() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 35, 36);
    }

    #[test]
    fn test_i32_constant_minus_private() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 35, 36);
    }

    #[test]
    fn test_i32_public_minus_constant() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 35, 36);
    }

    #[test]
    fn test_i32_private_minus_constant() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 35, 36);
    }

    #[test]
    fn test_i32_public_minus_public() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 35, 36);
    }

    #[test]
    fn test_i32_public_minus_private() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 35, 36);
    }

    #[test]
    fn test_i32_private_minus_public() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 35, 36);
    }

    #[test]
    fn test_i32_private_minus_private() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 35, 36);
    }

    // Tests for u64

    #[test]
    fn test_u64_constant_minus_constant() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_minus_public() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 67, 68);
    }

    #[test]
    fn test_u64_constant_minus_private() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 67, 68);
    }

    #[test]
    fn test_u64_public_minus_constant() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 67, 68);
    }

    #[test]
    fn test_u64_private_minus_constant() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 67, 68);
    }

    #[test]
    fn test_u64_public_minus_public() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 67, 68);
    }

    #[test]
    fn test_u64_public_minus_private() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 67, 68);
    }

    #[test]
    fn test_u64_private_minus_public() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 67, 68);
    }

    #[test]
    fn test_u64_private_minus_private() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 67, 68);
    }

    // Tests for i64

    #[test]
    fn test_i64_constant_minus_constant() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_minus_public() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 67, 68);
    }

    #[test]
    fn test_i64_constant_minus_private() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 67, 68);
    }

    #[test]
    fn test_i64_public_minus_constant() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 67, 68);
    }

    #[test]
    fn test_i64_private_minus_constant() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 67, 68);
    }

    #[test]
    fn test_i64_public_minus_public() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 67, 68);
    }

    #[test]
    fn test_i64_public_minus_private() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 67, 68);
    }

    #[test]
    fn test_i64_private_minus_public() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 67, 68);
    }

    #[test]
    fn test_i64_private_minus_private() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 67, 68);
    }

    // Tests for u128

    #[test]
    fn test_u128_constant_minus_constant() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_minus_public() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 131, 132);
    }

    #[test]
    fn test_u128_constant_minus_private() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 131, 132);
    }

    #[test]
    fn test_u128_public_minus_constant() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 131, 132);
    }

    #[test]
    fn test_u128_private_minus_constant() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 131, 132);
    }

    #[test]
    fn test_u128_public_minus_public() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 131, 132);
    }

    #[test]
    fn test_u128_public_minus_private() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 131, 132);
    }

    #[test]
    fn test_u128_private_minus_public() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 131, 132);
    }

    #[test]
    fn test_u128_private_minus_private() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 131, 132);
    }

    // Tests for i128

    #[test]
    fn test_i128_constant_minus_constant() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_minus_public() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 131, 132);
    }

    #[test]
    fn test_i128_constant_minus_private() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 131, 132);
    }

    #[test]
    fn test_i128_public_minus_constant() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 131, 132);
    }

    #[test]
    fn test_i128_private_minus_constant() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 131, 132);
    }

    #[test]
    fn test_i128_public_minus_public() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 131, 132);
    }

    #[test]
    fn test_i128_public_minus_private() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 131, 132);
    }

    #[test]
    fn test_i128_private_minus_public() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 131, 132);
    }

    #[test]
    fn test_i128_private_minus_private() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 131, 132);
    }
}
