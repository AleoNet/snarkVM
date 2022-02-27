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

use itertools::Itertools;

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
            let mut bits_le = Vec::with_capacity(I::BITS);
            let mut borrow = Boolean::new(Mode::Constant, false);

            // Perform a ripple-borrow subtractor on the bits.
            for (index, (a, b)) in self.bits_le.iter().zip_eq(other.bits_le.iter()).take(I::BITS).enumerate() {
                // Perform a full-subtractor on `a` and `b`.
                let (sum, next_borrow) = a.subtractor(&b, &borrow);
                bits_le.push(sum);

                // Determine if this iteration is the final round, and if the integer is signed.
                // This boolean is used to differentiate logic for the signed and unsigned cases.
                let is_msb_and_is_signed = index == (I::BITS - 1) && I::is_signed();

                if is_msb_and_is_signed {
                    // Signed case.
                    // Set the borrow as the XOR of the borrow bits from the MSB and (MSB - 1).
                    borrow = borrow.xor(&next_borrow);
                } else {
                    // Unsigned case.
                    borrow = next_borrow;
                };
            }

            // Ensure `borrow` is 0.
            E::assert_eq(borrow, E::zero());

            // Return the difference of `self` and `other`.
            Integer { bits_le, phantom: Default::default() }
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

    fn check_sub_checked<I: IntegerType, IC: IntegerTrait<I>>(
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

            let candidate = a.sub_checked(b);
            assert_eq!(expected, candidate.eject_value(), "{} != {} := {}", expected, candidate.eject_value(), case);

            assert_eq!(num_constants, Circuit::num_constants_in_scope(), "{} (num_constants)", case);
            assert_eq!(num_public, Circuit::num_public_in_scope(), "{} (num_public)", case);
            assert_eq!(num_private, Circuit::num_private_in_scope(), "{} (num_private)", case);
            assert_eq!(num_constraints, Circuit::num_constraints_in_scope(), "{} (num_constraints)", case);
            assert!(Circuit::is_satisfied(), "{} (is_satisfied)", case);
        });
    }

    fn check_underflow_halts<I: IntegerType + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        value_a: I,
        value_b: I,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, value_a);
        let b = Integer::new(mode_b, value_b);
        let result = std::panic::catch_unwind(|| a.sub_checked(&b));
        assert!(result.is_err());
    }

    fn check_underflow_fails<I: IntegerType + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        value_a: I,
        value_b: I,
    ) {
        let name = format!("Sub: {} - {} underflows", value_a, value_b);
        let a = Integer::<Circuit, I>::new(mode_a, value_a);
        let b = Integer::new(mode_b, value_b);
        Circuit::scoped(&name, || {
            let case = format!("({} - {})", a.eject_value(), b.eject_value());
            let _candidate = a.sub_checked(&b);
            assert!(!Circuit::is_satisfied(), "{} (!is_satisfied)", case);
        });
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
            let name = format!("Sub: a - b {}", i);
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: I = UniformRand::rand(&mut thread_rng());

            let a = Integer::<Circuit, I>::new(mode_a, first);
            let b = Integer::new(mode_b, second);

            match first.checked_sub(&second) {
                Some(expected) => check_sub_checked::<I, Integer<Circuit, I>>(&name, expected, &a, &b, num_constants, num_public, num_private, num_constraints),
                None => match (mode_a, mode_b) {
                    (Mode::Constant, Mode::Constant) => check_underflow_halts::<I>(mode_a, mode_b, first, second),
                    _ => check_underflow_fails::<I>(mode_a, mode_b, first, second)
                },
            }

            Circuit::reset()
        }
    }

    #[test]
    fn test_u8_constant_minus_constant() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
        check_underflow_halts::<I>(Mode::Constant, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_u8_constant_minus_public() {
        type I = u8;
        check_underflow_fails::<I>(Mode::Constant, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_u8_constant_minus_private() {
        type I = u8;
        check_underflow_fails::<I>(Mode::Constant, Mode::Private, I::MIN, I::one());
    }

    #[test]
    fn test_u8_public_minus_constant() {
        type I = u8;
        check_underflow_fails::<I>(Mode::Public, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_u8_private_minus_constant() {
        type I = u8;
        check_underflow_fails::<I>(Mode::Private, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_u8_public_minus_public() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Public, 1, 0, 37, 38);
        check_underflow_fails::<I>(Mode::Public, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_u8_public_minus_private() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Private, 1, 0, 37, 38);
        check_underflow_fails::<I>(Mode::Public, Mode::Private, I::MIN, I::one());
    }

    #[test]
    fn test_u8_private_minus_public() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Public, 1, 0, 37, 38);
        check_underflow_fails::<I>(Mode::Private, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_u8_private_minus_private() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Private, 1, 0, 37, 38);
        check_underflow_fails::<I>(Mode::Private, Mode::Private, I::MIN, I::one());
    }

    // Tests for i8

    #[test]
    fn test_i8_constant_minus_constant() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
        check_underflow_halts::<I>(Mode::Constant, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_i8_constant_minus_public() {
        type I = i8;
        check_underflow_fails::<I>(Mode::Constant, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_i8_constant_minus_private() {
        type I = i8;
        check_underflow_fails::<I>(Mode::Constant, Mode::Private, I::MIN, I::one());
    }

    #[test]
    fn test_i8_public_minus_constant() {
        type I = i8;
        check_underflow_fails::<I>(Mode::Public, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_i8_private_minus_constant() {
        type I = i8;
        check_underflow_fails::<I>(Mode::Private, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_i8_public_minus_public() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Public, 1, 0, 38, 39);
        check_underflow_fails::<I>(Mode::Public, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_i8_public_minus_private() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Private, 1, 0, 38, 39);
        check_underflow_fails::<I>(Mode::Public, Mode::Private, I::MIN, I::one());
    }

    #[test]
    fn test_i8_private_minus_public() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Public, 1, 0, 38, 39);
        check_underflow_fails::<I>(Mode::Private, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_i8_private_minus_private() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Private, 1, 0, 38, 39);
        check_underflow_fails::<I>(Mode::Private, Mode::Private, I::MIN, I::one());
    }

    // Tests for u16

    #[test]
    fn test_u16_constant_minus_constant() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
        check_underflow_halts::<I>(Mode::Constant, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_u16_constant_minus_public() {
        type I = u16;
        check_underflow_fails::<I>(Mode::Constant, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_u16_constant_minus_private() {
        type I = u16;
        check_underflow_fails::<I>(Mode::Constant, Mode::Private, I::MIN, I::one());
    }

    #[test]
    fn test_u16_public_minus_constant() {
        type I = u16;
        check_underflow_fails::<I>(Mode::Public, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_u16_private_minus_constant() {
        type I = u16;
        check_underflow_fails::<I>(Mode::Private, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_u16_public_minus_public() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Public, 1, 0, 77, 78);
        check_underflow_fails::<I>(Mode::Public, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_u16_public_minus_private() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Private, 1, 0, 77, 78);
        check_underflow_fails::<I>(Mode::Public, Mode::Private, I::MIN, I::one());
    }

    #[test]
    fn test_u16_private_minus_public() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Public, 1, 0, 77, 78);
        check_underflow_fails::<I>(Mode::Private, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_u16_private_minus_private() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Private, 1, 0, 77, 78);
        check_underflow_fails::<I>(Mode::Private, Mode::Private, I::MIN, I::one());
    }

    // Tests for i16

    #[test]
    fn test_i16_constant_minus_constant() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
        check_underflow_halts::<I>(Mode::Constant, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_i16_constant_minus_public() {
        type I = i16;
        check_underflow_fails::<I>(Mode::Constant, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_i16_constant_minus_private() {
        type I = i16;
        check_underflow_fails::<I>(Mode::Constant, Mode::Private, I::MIN, I::one());
    }

    #[test]
    fn test_i16_public_minus_constant() {
        type I = i16;
        check_underflow_fails::<I>(Mode::Public, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_i16_private_minus_constant() {
        type I = i16;
        check_underflow_fails::<I>(Mode::Private, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_i16_public_minus_public() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Public, 1, 0, 78, 79);
        check_underflow_fails::<I>(Mode::Public, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_i16_public_minus_private() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Private, 1, 0, 78, 79);
        check_underflow_fails::<I>(Mode::Public, Mode::Private, I::MIN, I::one());
    }

    #[test]
    fn test_i16_private_minus_public() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Public, 1, 0, 78, 79);
        check_underflow_fails::<I>(Mode::Private, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_i16_private_minus_private() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Private, 1, 0, 78, 79);
        check_underflow_fails::<I>(Mode::Private, Mode::Private, I::MIN, I::one());
    }

    // Tests for u32

    #[test]
    fn test_u32_constant_minus_constant() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
        check_underflow_halts::<I>(Mode::Constant, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_u32_constant_minus_public() {
        type I = u32;
        check_underflow_fails::<I>(Mode::Constant, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_u32_constant_minus_private() {
        type I = u32;
        check_underflow_fails::<I>(Mode::Constant, Mode::Private, I::MIN, I::one());
    }

    #[test]
    fn test_u32_public_minus_constant() {
        type I = u32;
        check_underflow_fails::<I>(Mode::Public, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_u32_private_minus_constant() {
        type I = u32;
        check_underflow_fails::<I>(Mode::Private, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_u32_public_minus_public() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Public, 1, 0, 157, 158);
        check_underflow_fails::<I>(Mode::Public, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_u32_public_minus_private() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Private, 1, 0, 157, 158);
        check_underflow_fails::<I>(Mode::Public, Mode::Private, I::MIN, I::one());
    }

    #[test]
    fn test_u32_private_minus_public() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Public, 1, 0, 157, 158);
        check_underflow_fails::<I>(Mode::Private, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_u32_private_minus_private() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Private, 1, 0, 157, 158);
        check_underflow_fails::<I>(Mode::Private, Mode::Private, I::MIN, I::one());
    }

    // Tests for i32

    #[test]
    fn test_i32_constant_minus_constant() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
        check_underflow_halts::<I>(Mode::Constant, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_i32_constant_minus_public() {
        type I = i32;
        check_underflow_fails::<I>(Mode::Constant, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_i32_constant_minus_private() {
        type I = i32;
        check_underflow_fails::<I>(Mode::Constant, Mode::Private, I::MIN, I::one());
    }

    #[test]
    fn test_i32_public_minus_constant() {
        type I = i32;
        check_underflow_fails::<I>(Mode::Public, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_i32_private_minus_constant() {
        type I = i32;
        check_underflow_fails::<I>(Mode::Private, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_i32_public_minus_public() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Public, 1, 0, 158, 159);
        check_underflow_fails::<I>(Mode::Public, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_i32_public_minus_private() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Private, 1, 0, 158, 159);
        check_underflow_fails::<I>(Mode::Public, Mode::Private, I::MIN, I::one());
    }

    #[test]
    fn test_i32_private_minus_public() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public, 1, 0, 158, 159);
        check_underflow_fails::<I>(Mode::Private, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_i32_private_minus_private() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Private, 1, 0, 158, 159);
        check_underflow_fails::<I>(Mode::Private, Mode::Private, I::MIN, I::one());
    }

    // Tests for u64

    #[test]
    fn test_u64_constant_minus_constant() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
        check_underflow_halts::<I>(Mode::Constant, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_u64_constant_minus_public() {
        type I = u64;
        check_underflow_fails::<I>(Mode::Constant, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_u64_constant_minus_private() {
        type I = u64;
        check_underflow_fails::<I>(Mode::Constant, Mode::Private, I::MIN, I::one());
    }

    #[test]
    fn test_u64_public_minus_constant() {
        type I = u64;
        check_underflow_fails::<I>(Mode::Public, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_u64_private_minus_constant() {
        type I = u64;
        check_underflow_fails::<I>(Mode::Private, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_u64_public_minus_public() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Public, 1, 0, 317, 318);
        check_underflow_fails::<I>(Mode::Public, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_u64_public_minus_private() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Private, 1, 0, 317, 318);
        check_underflow_fails::<I>(Mode::Public, Mode::Private, I::MIN, I::one());
    }

    #[test]
    fn test_u64_private_minus_public() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Public, 1, 0, 317, 318);
        check_underflow_fails::<I>(Mode::Private, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_u64_private_minus_private() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Private, 1, 0, 317, 318);
        check_underflow_fails::<I>(Mode::Private, Mode::Private, I::MIN, I::one());
    }

    // Tests for i64

    #[test]
    fn test_i64_constant_minus_constant() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
        check_underflow_halts::<I>(Mode::Constant, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_i64_constant_minus_public() {
        type I = i64;
        check_underflow_fails::<I>(Mode::Constant, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_i64_constant_minus_private() {
        type I = i64;
        check_underflow_fails::<I>(Mode::Constant, Mode::Private, I::MIN, I::one());
    }

    #[test]
    fn test_i64_public_minus_constant() {
        type I = i64;
        check_underflow_fails::<I>(Mode::Public, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_i64_private_minus_constant() {
        type I = i64;
        check_underflow_fails::<I>(Mode::Private, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_i64_public_minus_public() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Public, 1, 0, 318, 319);
        check_underflow_fails::<I>(Mode::Public, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_i64_public_minus_private() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Private, 1, 0, 318, 319);
        check_underflow_fails::<I>(Mode::Public, Mode::Private, I::MIN, I::one());
    }

    #[test]
    fn test_i64_private_minus_public() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Public, 1, 0, 318, 319);
        check_underflow_fails::<I>(Mode::Private, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_i64_private_minus_private() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Private, 1, 0, 318, 319);
        check_underflow_fails::<I>(Mode::Private, Mode::Private, I::MIN, I::one());
    }

    // Tests for u128

    #[test]
    fn test_u128_constant_minus_constant() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
        check_underflow_halts::<I>(Mode::Constant, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_u128_constant_minus_public() {
        type I = u128;
        check_underflow_fails::<I>(Mode::Constant, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_u128_constant_minus_private() {
        type I = u128;
        check_underflow_fails::<I>(Mode::Constant, Mode::Private, I::MIN, I::one());
    }

    #[test]
    fn test_u128_public_minus_constant() {
        type I = u128;
        check_underflow_fails::<I>(Mode::Public, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_u128_private_minus_constant() {
        type I = u128;
        check_underflow_fails::<I>(Mode::Private, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_u128_public_minus_public() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Public, 1, 0, 637, 638);
        check_underflow_fails::<I>(Mode::Public, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_u128_public_minus_private() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Private, 1, 0, 637, 638);
        check_underflow_fails::<I>(Mode::Public, Mode::Private, I::MIN, I::one());
    }

    #[test]
    fn test_u128_private_minus_public() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Public, 1, 0, 637, 638);
        check_underflow_fails::<I>(Mode::Private, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_u128_private_minus_private() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Private, 1, 0, 637, 638);
        check_underflow_fails::<I>(Mode::Private, Mode::Private, I::MIN, I::one());
    }

    // Tests for i128

    #[test]
    fn test_i128_constant_minus_constant() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
        check_underflow_halts::<I>(Mode::Constant, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_i128_constant_minus_public() {
        type I = i128;
        check_underflow_fails::<I>(Mode::Constant, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_i128_constant_minus_private() {
        type I = i128;
        check_underflow_fails::<I>(Mode::Constant, Mode::Private, I::MIN, I::one());
    }

    #[test]
    fn test_i128_public_minus_constant() {
        type I = i128;
        check_underflow_fails::<I>(Mode::Public, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_i128_private_minus_constant() {
        type I = i128;
        check_underflow_fails::<I>(Mode::Private, Mode::Constant, I::MIN, I::one());
    }

    #[test]
    fn test_i128_public_minus_public() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Public, 1, 0, 638, 639);
        check_underflow_fails::<I>(Mode::Public, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_i128_public_minus_private() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Private, 1, 0, 638, 639);
        check_underflow_fails::<I>(Mode::Public, Mode::Private, I::MIN, I::one());
    }

    #[test]
    fn test_i128_private_minus_public() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Public, 1, 0, 638, 639);
        check_underflow_fails::<I>(Mode::Private, Mode::Public, I::MIN, I::one());
    }

    #[test]
    fn test_i128_private_minus_private() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Private, 1, 0, 638, 639);
        check_underflow_fails::<I>(Mode::Private, Mode::Private, I::MIN, I::one());
    }
}
