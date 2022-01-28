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

impl<E: Environment, I: IntegerType> AddCheckedField<Self> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn add_checked_field(&self, other: &Integer<E, I>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the sum and return the new constant.
            match self.eject_value().checked_add(&other.eject_value()) {
                Some(value) => Integer::new(Mode::Constant, value),
                None => E::halt("Integer overflow on addition of two constants"),
            }
        } else {
            // Instead of adding the bits of `self` and `other` directly, the integers are
            // converted into a field elements and subtracted, before being converted back to integers.
            // Note: This is safe as the field is larger than the maximum integer type supported.
            let this = BaseField::from_bits_le(Mode::Private, &self.bits_le);
            let that = BaseField::from_bits_le(Mode::Private, &other.bits_le);
            let sum = this.add(that);

            // This is safe since we extract at least one bit from the field element.
            let mut bits_le = sum.extract_lower_k_bits_le(I::BITS + 1);
            let carry = bits_le.pop().unwrap();

            // Over/underflow checks are different for signed and unsigned addition.
            if I::is_signed() {
                // TODO (@pranav) Do we need an explicit check for this?
                // This is safe since I::BITS is always greater than 0.
                let self_msb = self.bits_le.last().unwrap();
                let other_msb = other.bits_le.last().unwrap();
                let sum_msb = bits_le.last().unwrap();

                let same_signs = (&self_msb).is_eq(&other_msb);
                let overflow = same_signs.and(&sum_msb.is_neq(self_msb));

                // For signed addition, overflow conditions are:
                //   - a > 0 && b > 0 && a + b < 0 (Overflow)
                //   - a < 0 && b < 0 && a + b > 0 (Underflow)
                //   - Note that if sign(a) != sign(b) then over/underflow is impossible.
                //   - Note that the result of an overflow and underflow must be negative and positive, respectively
                E::assert_eq(overflow, E::zero());
            } else {
                // For unsigned addition, we only need to check that the carry bit is zero.
                E::assert_eq(carry, E::zero());
            }

            // Return the sum of `self` and `other`.
            Integer {
                bits_le,
                phantom: Default::default(),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use num_traits::One;
    use rand::thread_rng;

    const ITERATIONS: usize = 128;

    #[rustfmt::skip]
    fn check_add_checked<I: IntegerType, IC: IntegerTrait<I>>(
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
            let case = format!("({} + {})", a.eject_value(), b.eject_value());

            let candidate = a.add_checked_field(b);
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := {}",
                expected,
                candidate.eject_value(),
                case
            );

            assert_eq!(num_constants, scope.num_constants_in_scope(), "{} (num_constants)", case);
            assert_eq!(num_public, scope.num_public_in_scope(), "{} (num_public)", case);
            assert_eq!(num_private, scope.num_private_in_scope(), "{} (num_private)", case);
            assert_eq!(num_constraints, scope.num_constraints_in_scope(), "{} (num_constraints)", case);
            assert!(Circuit::is_satisfied(), "{} (is_satisfied)", case);
        });
    }

    #[rustfmt::skip]
    fn check_overflow_halts<I: IntegerType + std::panic::RefUnwindSafe>(mode_a: Mode, mode_b: Mode, value_a: I, value_b: I) {
        let a = Integer::<Circuit, I>::new(mode_a, value_a);
        let b = Integer::new(mode_b, value_b);
        let result = std::panic::catch_unwind(|| a.add_checked_field(&b));
        assert!(result.is_err());

        let a = Integer::<Circuit, I>::new(mode_a, value_b);
        let b = Integer::new(mode_b, value_a);
        let result = std::panic::catch_unwind(|| a.add_checked_field(&b));
        assert!(result.is_err());
    }

    #[rustfmt::skip]
    fn check_overflow_fails<I: IntegerType + std::panic::RefUnwindSafe>(mode_a: Mode, mode_b: Mode, value_a: I, value_b: I) {
        {
            let name = format!("Add: {} + {} overflows", value_a, value_b);
            let a = Integer::<Circuit, I>::new(mode_a, value_a);
            let b = Integer::new(mode_b, value_b);
            Circuit::scoped(&name, |_| {
                let case = format!("({} + {})", a.eject_value(), b.eject_value());
                let _candidate = a.add_checked_field(&b);
                assert!(!Circuit::is_satisfied(), "{} (!is_satisfied)", case);
            });
        }
        {
            let name = format!("Add: {} + {} overflows", value_b, value_a);
            let a = Integer::<Circuit, I>::new(mode_a, value_b);
            let b = Integer::new(mode_b, value_a);
            Circuit::scoped(&name, |_| {
                let case = format!("({} + {})", a.eject_value(), b.eject_value());
                let _candidate = a.add_checked_field(&b);
                assert!(!Circuit::is_satisfied(), "{} (!is_satisfied)", case);
            });
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
        for i in 0..ITERATIONS {
            let name = format!("Add: {} + {} {}", mode_a, mode_b, i);
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: I = UniformRand::rand(&mut thread_rng());

            let a = Integer::<Circuit, I>::new(mode_a, first);
            let b = Integer::new(mode_b, second);

            match first.checked_add(&second) {
                Some(expected) => check_add_checked::<I, Integer<Circuit, I>>(&name, expected, &a, &b, num_constants, num_public, num_private, num_constraints),
                None => match (mode_a, mode_b) {
                    (Mode::Constant, Mode::Constant) => check_overflow_halts::<I>(mode_a, mode_b, first, second),
                    _ => check_overflow_fails::<I>(mode_a, mode_b, first, second)
                },
            }

            Circuit::reset_circuit()
        }
    }

    #[test]
    fn test_u8_constant_plus_constant() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
        check_overflow_halts::<I>(Mode::Constant, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_u8_constant_plus_public() {
        type I = u8;
        check_overflow_fails::<I>(Mode::Constant, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_u8_constant_plus_private() {
        type I = u8;
        check_overflow_fails::<I>(Mode::Constant, Mode::Private, I::MAX, I::one());
    }

    #[test]
    fn test_u8_public_plus_constant() {
        type I = u8;
        check_overflow_fails::<I>(Mode::Public, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_u8_private_plus_constant() {
        type I = u8;
        check_overflow_fails::<I>(Mode::Private, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_u8_public_plus_public() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 11, 13);
        check_overflow_fails::<I>(Mode::Public, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_u8_public_plus_private() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 11, 13);
        check_overflow_fails::<I>(Mode::Public, Mode::Private, I::MAX, I::one());
    }

    #[test]
    fn test_u8_private_plus_public() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 11, 13);
        check_overflow_fails::<I>(Mode::Private, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_u8_private_plus_private() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 11, 13);
        check_overflow_fails::<I>(Mode::Private, Mode::Private, I::MAX, I::one());
    }

    // Tests for i8

    #[test]
    fn test_i8_constant_plus_constant() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
        check_overflow_halts::<I>(Mode::Constant, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_i8_constant_plus_public() {
        type I = i8;
        check_overflow_fails::<I>(Mode::Constant, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_i8_constant_plus_private() {
        type I = i8;
        check_overflow_fails::<I>(Mode::Constant, Mode::Private, I::MAX, I::one());
    }

    #[test]
    fn test_i8_public_plus_constant() {
        type I = i8;
        check_overflow_fails::<I>(Mode::Public, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_i8_private_plus_constant() {
        type I = i8;
        check_overflow_fails::<I>(Mode::Private, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_i8_public_plus_public() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 14, 16);
        check_overflow_fails::<I>(Mode::Public, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_i8_public_plus_private() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 14, 16);
        check_overflow_fails::<I>(Mode::Public, Mode::Private, I::MAX, I::one());
    }

    #[test]
    fn test_i8_private_plus_public() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 14, 16);
        check_overflow_fails::<I>(Mode::Private, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_i8_private_plus_private() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 14, 16);
        check_overflow_fails::<I>(Mode::Private, Mode::Private, I::MAX, I::one());
    }

    // Tests for u16

    #[test]
    fn test_u16_constant_plus_constant() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
        check_overflow_halts::<I>(Mode::Constant, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_u16_constant_plus_public() {
        type I = u16;
        check_overflow_fails::<I>(Mode::Constant, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_u16_constant_plus_private() {
        type I = u16;
        check_overflow_fails::<I>(Mode::Constant, Mode::Private, I::MAX, I::one());
    }

    #[test]
    fn test_u16_public_plus_constant() {
        type I = u16;
        check_overflow_fails::<I>(Mode::Public, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_u16_private_plus_constant() {
        type I = u16;
        check_overflow_fails::<I>(Mode::Private, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_u16_public_plus_public() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 19, 21);
        check_overflow_fails::<I>(Mode::Public, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_u16_public_plus_private() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 19, 21);
        check_overflow_fails::<I>(Mode::Public, Mode::Private, I::MAX, I::one());
    }

    #[test]
    fn test_u16_private_plus_public() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 19, 21);
        check_overflow_fails::<I>(Mode::Private, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_u16_private_plus_private() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 19, 21);
        check_overflow_fails::<I>(Mode::Private, Mode::Private, I::MAX, I::one());
    }

    // Tests for i16

    #[test]
    fn test_i16_constant_plus_constant() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
        check_overflow_halts::<I>(Mode::Constant, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_i16_constant_plus_public() {
        type I = i16;
        check_overflow_fails::<I>(Mode::Constant, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_i16_constant_plus_private() {
        type I = i16;
        check_overflow_fails::<I>(Mode::Constant, Mode::Private, I::MAX, I::one());
    }

    #[test]
    fn test_i16_public_plus_constant() {
        type I = i16;
        check_overflow_fails::<I>(Mode::Public, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_i16_private_plus_constant() {
        type I = i16;
        check_overflow_fails::<I>(Mode::Private, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_i16_public_plus_public() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 22, 24);
        check_overflow_fails::<I>(Mode::Public, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_i16_public_plus_private() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 22, 24);
        check_overflow_fails::<I>(Mode::Public, Mode::Private, I::MAX, I::one());
    }

    #[test]
    fn test_i16_private_plus_public() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 22, 24);
        check_overflow_fails::<I>(Mode::Private, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_i16_private_plus_private() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 22, 24);
        check_overflow_fails::<I>(Mode::Private, Mode::Private, I::MAX, I::one());
    }

    // Tests for u32

    #[test]
    fn test_u32_constant_plus_constant() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
        check_overflow_halts::<I>(Mode::Constant, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_u32_constant_plus_public() {
        type I = u32;
        check_overflow_fails::<I>(Mode::Constant, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_u32_constant_plus_private() {
        type I = u32;
        check_overflow_fails::<I>(Mode::Constant, Mode::Private, I::MAX, I::one());
    }

    #[test]
    fn test_u32_public_plus_constant() {
        type I = u32;
        check_overflow_fails::<I>(Mode::Public, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_u32_private_plus_constant() {
        type I = u32;
        check_overflow_fails::<I>(Mode::Private, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_u32_public_plus_public() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 35, 37);
        check_overflow_fails::<I>(Mode::Public, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_u32_public_plus_private() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 35, 37);
        check_overflow_fails::<I>(Mode::Public, Mode::Private, I::MAX, I::one());
    }

    #[test]
    fn test_u32_private_plus_public() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 35, 37);
        check_overflow_fails::<I>(Mode::Private, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_u32_private_plus_private() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 35, 37);
        check_overflow_fails::<I>(Mode::Private, Mode::Private, I::MAX, I::one());
    }

    // Tests for i32

    #[test]
    fn test_i32_constant_plus_constant() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
        check_overflow_halts::<I>(Mode::Constant, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_i32_constant_plus_public() {
        type I = i32;
        check_overflow_fails::<I>(Mode::Constant, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_i32_constant_plus_private() {
        type I = i32;
        check_overflow_fails::<I>(Mode::Constant, Mode::Private, I::MAX, I::one());
    }

    #[test]
    fn test_i32_public_plus_constant() {
        type I = i32;
        check_overflow_fails::<I>(Mode::Public, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_i32_private_plus_constant() {
        type I = i32;
        check_overflow_fails::<I>(Mode::Private, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_i32_public_plus_public() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 38, 40);
        check_overflow_fails::<I>(Mode::Public, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_i32_public_plus_private() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 38, 40);
        check_overflow_fails::<I>(Mode::Public, Mode::Private, I::MAX, I::one());
    }

    #[test]
    fn test_i32_private_plus_public() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 38, 40);
        check_overflow_fails::<I>(Mode::Private, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_i32_private_plus_private() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 38, 40);
        check_overflow_fails::<I>(Mode::Private, Mode::Private, I::MAX, I::one());
    }

    // Tests for u64

    #[test]
    fn test_u64_constant_plus_constant() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
        check_overflow_halts::<I>(Mode::Constant, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_u64_constant_plus_public() {
        type I = u64;
        check_overflow_fails::<I>(Mode::Constant, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_u64_constant_plus_private() {
        type I = u64;
        check_overflow_fails::<I>(Mode::Constant, Mode::Private, I::MAX, I::one());
    }

    #[test]
    fn test_u64_public_plus_constant() {
        type I = u64;
        check_overflow_fails::<I>(Mode::Public, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_u64_private_plus_constant() {
        type I = u64;
        check_overflow_fails::<I>(Mode::Private, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_u64_public_plus_public() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 67, 69);
        check_overflow_fails::<I>(Mode::Public, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_u64_public_plus_private() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 67, 69);
        check_overflow_fails::<I>(Mode::Public, Mode::Private, I::MAX, I::one());
    }

    #[test]
    fn test_u64_private_plus_public() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 67, 69);
        check_overflow_fails::<I>(Mode::Private, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_u64_private_plus_private() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 67, 69);
        check_overflow_fails::<I>(Mode::Private, Mode::Private, I::MAX, I::one());
    }

    // Tests for i64

    #[test]
    fn test_i64_constant_plus_constant() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
        check_overflow_halts::<I>(Mode::Constant, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_i64_constant_plus_public() {
        type I = i64;
        check_overflow_fails::<I>(Mode::Constant, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_i64_constant_plus_private() {
        type I = i64;
        check_overflow_fails::<I>(Mode::Constant, Mode::Private, I::MAX, I::one());
    }

    #[test]
    fn test_i64_public_plus_constant() {
        type I = i64;
        check_overflow_fails::<I>(Mode::Public, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_i64_private_plus_constant() {
        type I = i64;
        check_overflow_fails::<I>(Mode::Private, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_i64_public_plus_public() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 70, 72);
        check_overflow_fails::<I>(Mode::Public, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_i64_public_plus_private() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 70, 72);
        check_overflow_fails::<I>(Mode::Public, Mode::Private, I::MAX, I::one());
    }

    #[test]
    fn test_i64_private_plus_public() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 70, 72);
        check_overflow_fails::<I>(Mode::Private, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_i64_private_plus_private() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 70, 72);
        check_overflow_fails::<I>(Mode::Private, Mode::Private, I::MAX, I::one());
    }

    // Tests for u128

    #[test]
    fn test_u128_constant_plus_constant() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
        check_overflow_halts::<I>(Mode::Constant, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_u128_constant_plus_public() {
        type I = u128;
        check_overflow_fails::<I>(Mode::Constant, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_u128_constant_plus_private() {
        type I = u128;
        check_overflow_fails::<I>(Mode::Constant, Mode::Private, I::MAX, I::one());
    }

    #[test]
    fn test_u128_public_plus_constant() {
        type I = u128;
        check_overflow_fails::<I>(Mode::Public, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_u128_private_plus_constant() {
        type I = u128;
        check_overflow_fails::<I>(Mode::Private, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_u128_public_plus_public() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 131, 133);
        check_overflow_fails::<I>(Mode::Public, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_u128_public_plus_private() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 131, 133);
        check_overflow_fails::<I>(Mode::Public, Mode::Private, I::MAX, I::one());
    }

    #[test]
    fn test_u128_private_plus_public() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 131, 133);
        check_overflow_fails::<I>(Mode::Private, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_u128_private_plus_private() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 131, 133);
        check_overflow_fails::<I>(Mode::Private, Mode::Private, I::MAX, I::one());
    }

    // Tests for i128

    #[test]
    fn test_i128_constant_plus_constant() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
        check_overflow_halts::<I>(Mode::Constant, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_i128_constant_plus_public() {
        type I = i128;
        check_overflow_fails::<I>(Mode::Constant, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_i128_constant_plus_private() {
        type I = i128;
        check_overflow_fails::<I>(Mode::Constant, Mode::Private, I::MAX, I::one());
    }

    #[test]
    fn test_i128_public_plus_constant() {
        type I = i128;
        check_overflow_fails::<I>(Mode::Public, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_i128_private_plus_constant() {
        type I = i128;
        check_overflow_fails::<I>(Mode::Private, Mode::Constant, I::MAX, I::one());
    }

    #[test]
    fn test_i128_public_plus_public() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 134, 136);
        check_overflow_fails::<I>(Mode::Public, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_i128_public_plus_private() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 134, 136);
        check_overflow_fails::<I>(Mode::Public, Mode::Private, I::MAX, I::one());
    }

    #[test]
    fn test_i128_private_plus_public() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 134, 136);
        check_overflow_fails::<I>(Mode::Private, Mode::Public, I::MAX, I::one());
    }

    #[test]
    fn test_i128_private_plus_private() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 134, 136);
        check_overflow_fails::<I>(Mode::Private, Mode::Private, I::MAX, I::one());
    }
}
