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

use itertools::Itertools;

impl<E: Environment, I: IntegerType> SubWrappedField<Self> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn sub_wrapped_field(&self, other: &Integer<E, I>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the difference and return the new constant.
            Integer::new(Mode::Constant, self.eject_value().wrapping_sub(&other.eject_value()))
        } else {
            if I::is_signed() {
                todo!()
            } else {
                // Instead of adding the bits of `self` and `other` directly, the integers are
                // converted into a field elements, and subtracted, before being converted back to integers.
                // Note: This is safe as the field is larger than the maximum integer type supported.
                let this = BaseField::from_bits_le(Mode::Private, &self.bits_le);
                let that = BaseField::from_bits_le(Mode::Private, &other.bits_le);

                // TODO (@pranav) Reduce number of constants by initializing values directly in the base field.
                // Initialize some constants.
                let max_integer = Integer::new(Mode::Constant, I::max_value());
                let max_field = BaseField::from_bits_le(Mode::Constant, &max_integer.bits_le);
                let one_field = BaseField::from_bits_le(Mode::Constant, &Self::one().bits_le);

                let difference = (&this).sub(&that);

                // In order to check for underflow, we check that
                // I::MAX + (a - b) does not overflow and does not equal I::MAX.
                // The check is done this way since it is cheaper to check for
                // overflow in the bits of the field.
                let max_plus_difference = max_field.add(&difference);
                let mut bits_le = max_plus_difference.extract_lower_k_bits_le(I::BITS + 1);

                // This is safe because we extract at least one bit.
                let carry = bits_le.pop().unwrap();
                let value = Integer {
                    bits_le,
                    phantom: Default::default(),
                };
                let underflow = (!carry).and(&value.is_neq(&max_integer));

                // If `underflow` then return I::max + (a - b) + 1, else return a - b.
                let result = BaseField::ternary(&underflow, &max_plus_difference.add(&one_field), &difference);
                let bits_le = result.extract_lower_k_bits_le(I::BITS);

                // Return the difference of `self` and `other`.
                Integer {
                    bits_le,
                    phantom: Default::default(),
                }
            }
        }
    }
}

#[rustfmt::skip]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use num_traits::One;
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
        Circuit::scoped(name, |scope| {
            let case = format!("({} - {})", a.eject_value(), b.eject_value());

            let candidate = a.sub_wrapped_field(b);
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := {}",
                expected,
                candidate.eject_value(),
                case
            );

            print!("Constants: {:?}, ", scope.num_constants_in_scope());
            print!("Public: {:?}, ", scope.num_public_in_scope());
            print!("Private: {:?}, ", scope.num_private_in_scope());
            print!("Constraints: {:?}\n", scope.num_constraints_in_scope());

            // assert_eq!(num_constants, scope.num_constants_in_scope(), "{} (num_constants)", case);
            // assert_eq!(num_public, scope.num_public_in_scope(), "{} (num_public)", case);
            // assert_eq!(num_private, scope.num_private_in_scope(), "{} (num_private)", case);
            // assert_eq!(num_constraints, scope.num_constraints_in_scope(), "{} (num_constraints)", case);
            assert!(Circuit::is_satisfied(), "{} (is_satisfied)", case);
        });
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

        // Check that underflow wraps successfully.
        check_underflow::<I>(I::MIN, I::one(), I::MAX, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
    }

    #[test]
    fn test_u8_constant_minus_constant() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_minus_public() {
        type I = u8;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Constant, Mode::Public, 1, 0, 19, 19);
    }

    #[test]
    fn test_u8_constant_minus_private() {
        type I = u8;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Constant, Mode::Private, 1, 0, 19, 19);
    }

    #[test]
    fn test_u8_public_minus_constant() {
        type I = u8;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Public, Mode::Constant, 1, 0, 13, 13);
    }

    #[test]
    fn test_u8_private_minus_constant() {
        type I = u8;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Private, Mode::Constant, 1, 0, 13, 13);
    }

    #[test]
    fn test_u8_public_minus_public() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Public, 1, 0, 34, 34);
    }

    #[test]
    fn test_u8_public_minus_private() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Private, 1, 0, 34, 34);
    }

    #[test]
    fn test_u8_private_minus_public() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Public, 1, 0, 34, 34);
    }

    #[test]
    fn test_u8_private_minus_private() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Private, 1, 0, 34, 34);
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
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Constant, Mode::Public, 1, 0, 19, 19);
    }

    #[test]
    fn test_i8_constant_minus_private() {
        type I = i8;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Constant, Mode::Private, 1, 0, 19, 19);
    }

    #[test]
    fn test_i8_public_minus_constant() {
        type I = i8;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Public, Mode::Constant, 1, 0, 13, 13);
    }

    #[test]
    fn test_i8_private_minus_constant() {
        type I = i8;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Private, Mode::Constant, 1, 0, 13, 13);
    }

    #[test]
    fn test_i8_public_minus_public() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Public, 1, 0, 34, 34);
    }

    #[test]
    fn test_i8_public_minus_private() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Private, 1, 0, 34, 34);
    }

    #[test]
    fn test_i8_private_minus_public() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Public, 1, 0, 34, 34);
    }

    #[test]
    fn test_i8_private_minus_private() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Private, 1, 0, 34, 34);
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
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Constant, Mode::Public, 1, 0, 43, 43);
    }

    #[test]
    fn test_u16_constant_minus_private() {
        type I = u16;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Constant, Mode::Private, 1, 0, 43, 43);
    }

    #[test]
    fn test_u16_public_minus_constant() {
        type I = u16;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Public, Mode::Constant, 1, 0, 29, 29);
    }

    #[test]
    fn test_u16_private_minus_constant() {
        type I = u16;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Private, Mode::Constant, 1, 0, 29, 29);
    }

    #[test]
    fn test_u16_public_minus_public() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Public, 1, 0, 74, 74);
    }

    #[test]
    fn test_u16_public_minus_private() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Private, 1, 0, 74, 74);
    }

    #[test]
    fn test_u16_private_minus_public() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Public, 1, 0, 74, 74);
    }

    #[test]
    fn test_u16_private_minus_private() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Private, 1, 0, 74, 74);
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
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Constant, Mode::Public, 1, 0, 43, 43);
    }

    #[test]
    fn test_i16_constant_minus_private() {
        type I = i16;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Constant, Mode::Private, 1, 0, 43, 43);
    }

    #[test]
    fn test_i16_public_minus_constant() {
        type I = i16;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Public, Mode::Constant, 1, 0, 29, 29);
    }

    #[test]
    fn test_i16_private_minus_constant() {
        type I = i16;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Private, Mode::Constant, 1, 0, 29, 29);
    }

    #[test]
    fn test_i16_public_minus_public() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Public, 1, 0, 74, 74);
    }

    #[test]
    fn test_i16_public_minus_private() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Private, 1, 0, 74, 74);
    }

    #[test]
    fn test_i16_private_minus_public() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Public, 1, 0, 74, 74);
    }

    #[test]
    fn test_i16_private_minus_private() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Private, 1, 0, 74, 74);
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
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Constant, Mode::Public, 1, 0, 91, 91);
    }

    #[test]
    fn test_u32_constant_minus_private() {
        type I = u32;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Constant, Mode::Private, 1, 0, 91, 91);
    }

    #[test]
    fn test_u32_public_minus_constant() {
        type I = u32;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Public, Mode::Constant, 1, 0, 61, 61);
    }

    #[test]
    fn test_u32_private_minus_constant() {
        type I = u32;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Private, Mode::Constant, 1, 0, 61, 61);
    }

    #[test]
    fn test_u32_public_minus_public() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Public, 1, 0, 154, 154);
    }

    #[test]
    fn test_u32_public_minus_private() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Private, 1, 0, 154, 154);
    }

    #[test]
    fn test_u32_private_minus_public() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Public, 1, 0, 154, 154);
    }

    #[test]
    fn test_u32_private_minus_private() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Private, 1, 0, 154, 154);
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
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Constant, Mode::Public, 1, 0, 91, 91);
    }

    #[test]
    fn test_i32_constant_minus_private() {
        type I = i32;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Constant, Mode::Private, 1, 0, 91, 91);
    }

    #[test]
    fn test_i32_public_minus_constant() {
        type I = i32;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Public, Mode::Constant, 1, 0, 61, 61);
    }

    #[test]
    fn test_i32_private_minus_constant() {
        type I = i32;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Private, Mode::Constant, 1, 0, 61, 61);
    }

    #[test]
    fn test_i32_public_minus_public() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Public, 1, 0, 154, 154);
    }

    #[test]
    fn test_i32_public_minus_private() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Private, 1, 0, 154, 154);
    }

    #[test]
    fn test_i32_private_minus_public() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public, 1, 0, 154, 154);
    }

    #[test]
    fn test_i32_private_minus_private() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Private, 1, 0, 154, 154);
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
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Constant, Mode::Public, 1, 0, 187, 187);
    }

    #[test]
    fn test_u64_constant_minus_private() {
        type I = u64;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Constant, Mode::Private, 1, 0, 187, 187);
    }

    #[test]
    fn test_u64_public_minus_constant() {
        type I = u64;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Public, Mode::Constant, 1, 0, 125, 125);
    }

    #[test]
    fn test_u64_private_minus_constant() {
        type I = u64;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Private, Mode::Constant, 1, 0, 125, 125);
    }

    #[test]
    fn test_u64_public_minus_public() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Public, 1, 0, 314, 314);
    }

    #[test]
    fn test_u64_public_minus_private() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Private, 1, 0, 314, 314);
    }

    #[test]
    fn test_u64_private_minus_public() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Public, 1, 0, 314, 314);
    }

    #[test]
    fn test_u64_private_minus_private() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Private, 1, 0, 314, 314);
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
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Constant, Mode::Public, 1, 0, 187, 187);
    }

    #[test]
    fn test_i64_constant_minus_private() {
        type I = i64;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Constant, Mode::Private, 1, 0, 187, 187);
    }

    #[test]
    fn test_i64_public_minus_constant() {
        type I = i64;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Public, Mode::Constant, 1, 0, 125, 125);
    }

    #[test]
    fn test_i64_private_minus_constant() {
        type I = i64;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Private, Mode::Constant, 1, 0, 125, 125);
    }

    #[test]
    fn test_i64_public_minus_public() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Public, 1, 0, 314, 314);
    }

    #[test]
    fn test_i64_public_minus_private() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Private, 1, 0, 314, 314);
    }

    #[test]
    fn test_i64_private_minus_public() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Public, 1, 0, 314, 314);
    }

    #[test]
    fn test_i64_private_minus_private() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Private, 1, 0, 314, 314);
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
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Constant, Mode::Public, 1, 0, 379, 379);
    }

    #[test]
    fn test_u128_constant_minus_private() {
        type I = u128;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Constant, Mode::Private, 1, 0, 379, 379);
    }

    #[test]
    fn test_u128_public_minus_constant() {
        type I = u128;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Public, Mode::Constant, 1, 0, 253, 253);
    }

    #[test]
    fn test_u128_private_minus_constant() {
        type I = u128;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Private, Mode::Constant, 1, 0, 253, 253);
    }

    #[test]
    fn test_u128_public_minus_public() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Public, 1, 0, 634, 634);
    }

    #[test]
    fn test_u128_public_minus_private() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Private, 1, 0, 634, 634);
    }

    #[test]
    fn test_u128_private_minus_public() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Public, 1, 0, 634, 634);
    }

    #[test]
    fn test_u128_private_minus_private() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Private, 1, 0, 634, 634);
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
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Constant, Mode::Public, 1, 0, 379, 379);
    }

    #[test]
    fn test_i128_constant_minus_private() {
        type I = i128;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Constant, Mode::Private, 1, 0, 379, 379);
    }

    #[test]
    fn test_i128_public_minus_constant() {
        type I = i128;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Public, Mode::Constant, 1, 0, 253, 253);
    }

    #[test]
    fn test_i128_private_minus_constant() {
        type I = i128;
        check_underflow::<I>(I::MIN, I::one(), I::MAX, Mode::Private, Mode::Constant, 1, 0, 253, 253);
    }

    #[test]
    fn test_i128_public_minus_public() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Public, 1, 0, 634, 634);
    }

    #[test]
    fn test_i128_public_minus_private() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Private, 1, 0, 634, 634);
    }

    #[test]
    fn test_i128_private_minus_public() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Public, 1, 0, 634, 634);
    }

    #[test]
    fn test_i128_private_minus_private() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Private, 1, 0, 634, 634);
    }
}
