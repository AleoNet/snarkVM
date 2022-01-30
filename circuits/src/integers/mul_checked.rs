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
        } else {
            todo!()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 128;

    #[rustfmt::skip]
    fn check_mul_checked<I: IntegerType, IC: IntegerTrait<I>>(
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
            let case = format!("({} * {})", a.eject_value(), b.eject_value());

            let candidate = a.mul_checked(b);
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
    }

    #[rustfmt::skip]
    fn check_overflow_halts<I: IntegerType + std::panic::RefUnwindSafe>(mode_a: Mode, mode_b: Mode, value_a: I, value_b: I) {
        let a = Integer::<Circuit, I>::new(mode_a, value_a);
        let b = Integer::new(mode_b, value_b);
        let result = std::panic::catch_unwind(|| a.mul_checked(&b));
        assert!(result.is_err());

        let a = Integer::<Circuit, I>::new(mode_a, value_b);
        let b = Integer::new(mode_b, value_a);
        let result = std::panic::catch_unwind(|| a.mul_checked(&b));
        assert!(result.is_err());
    }

    #[rustfmt::skip]
    fn check_overflow_fails<I: IntegerType + std::panic::RefUnwindSafe>(mode_a: Mode, mode_b: Mode, value_a: I, value_b: I) {
        {
            let name = format!("Mul: {} * {} overflows", value_a, value_b);
            let a = Integer::<Circuit, I>::new(mode_a, value_a);
            let b = Integer::new(mode_b, value_b);
            Circuit::scoped(&name, || {
                let case = format!("({} * {})", a.eject_value(), b.eject_value());
                let _candidate = a.mul_checked(&b);
                assert!(!Circuit::is_satisfied(), "{} (!is_satisfied)", case);
            });
        }
        {
            let name = format!("Mul: {} * {} overflows", value_b, value_a);
            let a = Integer::<Circuit, I>::new(mode_a, value_b);
            let b = Integer::new(mode_b, value_a);
            Circuit::scoped(&name, || {
                let case = format!("({} * {})", a.eject_value(), b.eject_value());
                let _candidate = a.mul_checked(&b);
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
        let check_overflow = |value_a, value_b| match (mode_a, mode_b) {
            (Mode::Constant, Mode::Constant) => check_overflow_halts::<I>(mode_a, mode_b, value_a, value_b),
            (_,_) => check_overflow_fails::<I>(mode_a, mode_b, value_a, value_b),
        };

        for i in 0..ITERATIONS {
            let name = format!("Mul: {} * {} {}", mode_a, mode_b, i);
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: I = UniformRand::rand(&mut thread_rng());

            let a = Integer::<Circuit, I>::new(mode_a, first);
            let b = Integer::new(mode_b, second);

            match first.checked_mul(&second) {
                Some(expected) => check_mul_checked::<I, Integer<Circuit, I>>(&name, expected, &a, &b, num_constants, num_public, num_private, num_constraints),
                None => check_overflow(first, second),
            }

            Circuit::reset()
        }

        match I::is_signed() {
            true => {
                // Overflow
                check_overflow(I::MAX, I::one());
                check_overflow(I::one(), I::MAX);

                // Underflow
                check_overflow(I::MIN, I::zero() - I::one());
                check_overflow(I::zero() - I::one(), I::MIN);
            },
            false => {
                // Overflow
                check_overflow(I::MAX, I::one());
                check_overflow(I::one(), I::MAX);
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
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 11, 13);
    }

    #[test]
    fn test_u8_constant_times_private() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 11, 13);
    }

    #[test]
    fn test_u8_public_times_constant() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 11, 13);
    }

    #[test]
    fn test_u8_private_times_constant() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 11, 13);
    }

    #[test]
    fn test_u8_public_times_public() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 11, 13);
    }

    #[test]
    fn test_u8_public_times_private() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 11, 13);
    }

    #[test]
    fn test_u8_private_times_public() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 11, 13);
    }

    #[test]
    fn test_u8_private_times_private() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 11, 13);
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
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 12, 14);
    }

    #[test]
    fn test_i8_constant_times_private() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 12, 14);
    }

    #[test]
    fn test_i8_public_times_constant() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 13, 15);
    }

    #[test]
    fn test_i8_private_times_constant() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 13, 15);
    }

    #[test]
    fn test_i8_public_times_public() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 14, 16);
    }

    #[test]
    fn test_i8_public_times_private() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 14, 16);
    }

    #[test]
    fn test_i8_private_times_public() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 14, 16);
    }

    #[test]
    fn test_i8_private_times_private() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 14, 16);
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
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 19, 21);
    }

    #[test]
    fn test_u16_constant_times_private() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 19, 21);
    }

    #[test]
    fn test_u16_public_times_constant() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 19, 21);
    }

    #[test]
    fn test_u16_private_times_constant() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 19, 21);
    }

    #[test]
    fn test_u16_public_times_public() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 19, 21);
    }

    #[test]
    fn test_u16_public_times_private() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 19, 21);
    }

    #[test]
    fn test_u16_private_times_public() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 19, 21);
    }

    #[test]
    fn test_u16_private_times_private() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 19, 21);
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
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 20, 22);
    }

    #[test]
    fn test_i16_constant_times_private() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 20, 22);
    }

    #[test]
    fn test_i16_public_times_constant() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 21, 23);
    }

    #[test]
    fn test_i16_private_times_constant() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 21, 23);
    }

    #[test]
    fn test_i16_public_times_public() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 22, 24);
    }

    #[test]
    fn test_i16_public_times_private() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 22, 24);
    }

    #[test]
    fn test_i16_private_times_public() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 22, 24);
    }

    #[test]
    fn test_i16_private_times_private() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 22, 24);
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
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 35, 37);
    }

    #[test]
    fn test_u32_constant_times_private() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 35, 37);
    }

    #[test]
    fn test_u32_public_times_constant() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 35, 37);
    }

    #[test]
    fn test_u32_private_times_constant() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 35, 37);
    }

    #[test]
    fn test_u32_public_times_public() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 35, 37);
    }

    #[test]
    fn test_u32_public_times_private() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 35, 37);
    }

    #[test]
    fn test_u32_private_times_public() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 35, 37);
    }

    #[test]
    fn test_u32_private_times_private() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 35, 37);
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
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 36, 38);
    }

    #[test]
    fn test_i32_constant_times_private() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 36, 38);
    }

    #[test]
    fn test_i32_public_times_constant() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 37, 39);
    }

    #[test]
    fn test_i32_private_times_constant() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 37, 39);
    }

    #[test]
    fn test_i32_public_times_public() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 38, 40);
    }

    #[test]
    fn test_i32_public_times_private() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 38, 40);
    }

    #[test]
    fn test_i32_private_times_public() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 38, 40);
    }

    #[test]
    fn test_i32_private_times_private() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 38, 40);
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
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 67, 69);
    }

    #[test]
    fn test_u64_constant_times_private() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 67, 69);
    }

    #[test]
    fn test_u64_public_times_constant() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 67, 69);
    }

    #[test]
    fn test_u64_private_times_constant() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 67, 69);
    }

    #[test]
    fn test_u64_public_times_public() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 67, 69);
    }

    #[test]
    fn test_u64_public_times_private() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 67, 69);
    }

    #[test]
    fn test_u64_private_times_public() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 67, 69);
    }

    #[test]
    fn test_u64_private_times_private() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 67, 69);
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
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 68, 70);
    }

    #[test]
    fn test_i64_constant_times_private() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 68, 70);
    }

    #[test]
    fn test_i64_public_times_constant() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 69, 71);
    }

    #[test]
    fn test_i64_private_times_constant() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 69, 71);
    }

    #[test]
    fn test_i64_public_times_public() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 70, 72);
    }

    #[test]
    fn test_i64_public_times_private() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 70, 72);
    }

    #[test]
    fn test_i64_private_times_public() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 70, 72);
    }

    #[test]
    fn test_i64_private_times_private() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 70, 72);
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
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 131, 133);
    }

    #[test]
    fn test_u128_constant_times_private() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 131, 133);
    }

    #[test]
    fn test_u128_public_times_constant() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 131, 133);
    }

    #[test]
    fn test_u128_private_times_constant() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 131, 133);
    }

    #[test]
    fn test_u128_public_times_public() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 131, 133);
    }

    #[test]
    fn test_u128_public_times_private() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 131, 133);
    }

    #[test]
    fn test_u128_private_times_public() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 131, 133);
    }

    #[test]
    fn test_u128_private_times_private() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 131, 133);
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
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 132, 134);
    }

    #[test]
    fn test_i128_constant_times_private() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 132, 134);
    }

    #[test]
    fn test_i128_public_times_constant() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 133, 135);
    }

    #[test]
    fn test_i128_private_times_constant() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 133, 135);
    }

    #[test]
    fn test_i128_public_times_public() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 134, 136);
    }

    #[test]
    fn test_i128_public_times_private() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 134, 136);
    }

    #[test]
    fn test_i128_private_times_public() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 134, 136);
    }

    #[test]
    fn test_i128_private_times_private() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 134, 136);
    }
}
