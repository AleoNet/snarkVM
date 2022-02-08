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

impl<E: Environment, I: IntegerType> SubChecked<Self> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn sub_checked(&self, other: &Integer<E, I>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the difference and return the new constant.
            match self.eject_value().checked_sub(&other.eject_value()) {
                Some(value) => Integer::new(Mode::Constant, value),
                None => E::halt("Integer underflow on subtraction of two constants"),
            }
        } else {
            // Instead of subtracting the bits of `self` and `other` directly, the integers are
            // converted into a field elements, and subtracted, before being converted back to integers.
            // Note: This is safe as the field is larger than the maximum integer type supported.
            let minuend = BaseField::from_bits_le(Mode::Private, &self.bits_le);
            let subtrahend =
                BaseField::from_bits_le(Mode::Private, &other.bits_le.iter().map(|b| !b).collect::<Vec<_>>());
            let difference = minuend + &subtrahend + BaseField::one();

            // Extract the integer bits from the field element, with a carry bit.
            let field_bits = difference.to_lower_bits_le(I::BITS + 1);
            let (carry, bits_le) = match field_bits.split_last() {
                Some((carry, bits_le)) => (carry, bits_le),
                None => E::halt("Malformed difference detected during integer subtraction"),
            };

            // Underflow conditions are different for signed and unsigned integers.
            match I::is_signed() {
                true => {
                    // This is safe since I::BITS is always greater than 0.
                    let minuend_msb = self.bits_le.last().unwrap();
                    let subtrahend_msb = other.bits_le.last().unwrap();
                    let result_msb = bits_le.last().unwrap();

                    let is_different_signs = minuend_msb.is_neq(subtrahend_msb);
                    let is_underflow = is_different_signs.and(&result_msb.is_eq(subtrahend_msb));

                    // For signed subtraction, overflow and underflow conditions are:
                    //   - a > 0 && b < 0 && a - b > 0 (Overflow)
                    //   - a < 0 && b > 0 && a - b < 0 (Underflow)
                    //   - Note: if sign(a) == sign(b) then over/underflow is impossible.
                    //   - Note: the result of an overflow and underflow must be negative and positive, respectively.
                    E::assert_eq(is_underflow, E::zero());
                }
                false => {
                    // For unsigned subtraction, ensure the carry bit is one.
                    E::assert_eq(carry, E::one());
                }
            }

            // Return the difference of `self` and `other`.
            Integer { bits_le: bits_le.to_vec(), phantom: Default::default() }
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
    use std::{ops::Range, panic::RefUnwindSafe};

    const ITERATIONS: usize = 128;

    #[rustfmt::skip]
    fn check_sub<I: IntegerType + std::panic::RefUnwindSafe>(
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
        let case = format!("({} - {})", a.eject_value(), b.eject_value());
        match first.checked_sub(&second) {
            Some(value) => check_binary_operation_passes(name, &case, value, &a, &b, Integer::sub_checked, num_constants, num_public, num_private, num_constraints),
            None => {
                match (mode_a, mode_b) {
                    (Mode::Constant, Mode::Constant) => check_binary_operation_halts(&a, &b, Integer::sub_checked),
                    _ => check_binary_operation_fails(name, &case, &a, &b, Integer::sub_checked, num_constants, num_public, num_private, num_constraints)
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
        let check_sub = | name: &str, first: I, second: I | check_sub(name, first, second, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);

        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: I = UniformRand::rand(&mut thread_rng());

            let name = format!("Sub: a - b {}", i);
            check_sub(&name, first, second);
        }

        match I::is_signed() {
            // Check overflow and underflow conditions for signed integers
            true => {
                // Overflow
                check_sub("MAX - (-1)", I::MAX, I::zero() - I::one());

                // Underflow
                check_sub("MIN - 1", I::MIN, I::one());
            },
            false => {
                // Underflow
                check_sub("MIN - 1", I::MIN, I::one());
            }
        }
    }

    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) where
        Range<I>: Iterator<Item = I>,
    {
        for first in I::MIN..I::MAX {
            for second in I::MIN..I::MAX {
                let name = format!("Sub: ({} - {})", first, second);
                check_sub(
                    &name,
                    first,
                    second,
                    mode_a,
                    mode_b,
                    num_constants,
                    num_public,
                    num_private,
                    num_constraints,
                );
            }
        }
    }

    // Tests for u8.

    #[test]
    fn test_u8_constant_minus_constant() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_minus_public() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 11, 13);
    }

    #[test]
    fn test_u8_constant_minus_private() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 11, 13);
    }

    #[test]
    fn test_u8_public_minus_constant() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 11, 13);
    }

    #[test]
    fn test_u8_private_minus_constant() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 11, 13);
    }

    #[test]
    fn test_u8_public_minus_public() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 11, 13);
    }

    #[test]
    fn test_u8_public_minus_private() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 11, 13);
    }

    #[test]
    fn test_u8_private_minus_public() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 11, 13);
    }

    #[test]
    fn test_u8_private_minus_private() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 11, 13);
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
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 13, 15);
    }

    #[test]
    fn test_i8_constant_minus_private() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 13, 15);
    }

    #[test]
    fn test_i8_public_minus_constant() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 12, 14);
    }

    #[test]
    fn test_i8_private_minus_constant() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 12, 14);
    }

    #[test]
    fn test_i8_public_minus_public() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 14, 16);
    }

    #[test]
    fn test_i8_public_minus_private() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 14, 16);
    }

    #[test]
    fn test_i8_private_minus_public() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 14, 16);
    }

    #[test]
    fn test_i8_private_minus_private() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 14, 16);
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
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 19, 21);
    }

    #[test]
    fn test_u16_constant_minus_private() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 19, 21);
    }

    #[test]
    fn test_u16_public_minus_constant() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 19, 21);
    }

    #[test]
    fn test_u16_private_minus_constant() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 19, 21);
    }

    #[test]
    fn test_u16_public_minus_public() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 19, 21);
    }

    #[test]
    fn test_u16_public_minus_private() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 19, 21);
    }

    #[test]
    fn test_u16_private_minus_public() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 19, 21);
    }

    #[test]
    fn test_u16_private_minus_private() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 19, 21);
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
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 21, 23);
    }

    #[test]
    fn test_i16_constant_minus_private() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 21, 23);
    }

    #[test]
    fn test_i16_public_minus_constant() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 20, 22);
    }

    #[test]
    fn test_i16_private_minus_constant() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 20, 22);
    }

    #[test]
    fn test_i16_public_minus_public() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 22, 24);
    }

    #[test]
    fn test_i16_public_minus_private() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 22, 24);
    }

    #[test]
    fn test_i16_private_minus_public() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 22, 24);
    }

    #[test]
    fn test_i16_private_minus_private() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 22, 24);
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
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 35, 37);
    }

    #[test]
    fn test_u32_constant_minus_private() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 35, 37);
    }

    #[test]
    fn test_u32_public_minus_constant() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 35, 37);
    }

    #[test]
    fn test_u32_private_minus_constant() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 35, 37);
    }

    #[test]
    fn test_u32_public_minus_public() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 35, 37);
    }

    #[test]
    fn test_u32_public_minus_private() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 35, 37);
    }

    #[test]
    fn test_u32_private_minus_public() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 35, 37);
    }

    #[test]
    fn test_u32_private_minus_private() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 35, 37);
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
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 37, 39);
    }

    #[test]
    fn test_i32_constant_minus_private() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 37, 39);
    }

    #[test]
    fn test_i32_public_minus_constant() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 36, 38);
    }

    #[test]
    fn test_i32_private_minus_constant() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 36, 38);
    }

    #[test]
    fn test_i32_public_minus_public() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 38, 40);
    }

    #[test]
    fn test_i32_public_minus_private() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 38, 40);
    }

    #[test]
    fn test_i32_private_minus_public() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 38, 40);
    }

    #[test]
    fn test_i32_private_minus_private() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 38, 40);
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
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 67, 69);
    }

    #[test]
    fn test_u64_constant_minus_private() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 67, 69);
    }

    #[test]
    fn test_u64_public_minus_constant() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 67, 69);
    }

    #[test]
    fn test_u64_private_minus_constant() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 67, 69);
    }

    #[test]
    fn test_u64_public_minus_public() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 67, 69);
    }

    #[test]
    fn test_u64_public_minus_private() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 67, 69);
    }

    #[test]
    fn test_u64_private_minus_public() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 67, 69);
    }

    #[test]
    fn test_u64_private_minus_private() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 67, 69);
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
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 69, 71);
    }

    #[test]
    fn test_i64_constant_minus_private() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 69, 71);
    }

    #[test]
    fn test_i64_public_minus_constant() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 68, 70);
    }

    #[test]
    fn test_i64_private_minus_constant() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 68, 70);
    }

    #[test]
    fn test_i64_public_minus_public() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 70, 72);
    }

    #[test]
    fn test_i64_public_minus_private() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 70, 72);
    }

    #[test]
    fn test_i64_private_minus_public() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 70, 72);
    }

    #[test]
    fn test_i64_private_minus_private() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 70, 72);
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
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 131, 133);
    }

    #[test]
    fn test_u128_constant_minus_private() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 131, 133);
    }

    #[test]
    fn test_u128_public_minus_constant() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 131, 133);
    }

    #[test]
    fn test_u128_private_minus_constant() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 131, 133);
    }

    #[test]
    fn test_u128_public_minus_public() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 131, 133);
    }

    #[test]
    fn test_u128_public_minus_private() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 131, 133);
    }

    #[test]
    fn test_u128_private_minus_public() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 131, 133);
    }

    #[test]
    fn test_u128_private_minus_private() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 131, 133);
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
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 133, 135);
    }

    #[test]
    fn test_i128_constant_minus_private() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 133, 135);
    }

    #[test]
    fn test_i128_public_minus_constant() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 132, 134);
    }

    #[test]
    fn test_i128_private_minus_constant() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 132, 134);
    }

    #[test]
    fn test_i128_public_minus_public() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 134, 136);
    }

    #[test]
    fn test_i128_public_minus_private() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 134, 136);
    }

    #[test]
    fn test_i128_private_minus_public() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 134, 136);
    }

    #[test]
    fn test_i128_private_minus_private() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 134, 136);
    }

    // Exhaustive tests for u8.

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_minus_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_minus_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Public, 2, 0, 11, 13);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_minus_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Private, 2, 0, 11, 13);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_minus_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Constant, 2, 0, 11, 13);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_minus_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Constant, 2, 0, 11, 13);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_minus_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Public, 2, 0, 11, 13);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_minus_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Private, 2, 0, 11, 13);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_minus_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Public, 2, 0, 11, 13);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_minus_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Private, 2, 0, 11, 13);
    }

    // Tests for i8

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_minus_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_minus_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Public, 2, 0, 13, 15);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_minus_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Private, 2, 0, 13, 15);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_minus_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Constant, 2, 0, 12, 14);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_minus_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Constant, 2, 0, 12, 14);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_minus_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Public, 2, 0, 14, 16);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_minus_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Private, 2, 0, 14, 16);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_minus_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Public, 2, 0, 14, 16);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_minus_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Private, 2, 0, 14, 16);
    }
}
