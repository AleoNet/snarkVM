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

impl<E: Environment, I: IntegerType> PowChecked for Integer<E, I> {
    type Exponent = Integer<E, u32>;
    type Output = Self;

    #[inline]
    fn pow_checked(&self, other: &Self::Exponent) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the result and return the new constant.
            match self.eject_value().checked_pow(other.eject_value()) {
                Some(value) => Integer::new(Mode::Constant, value),
                None => E::halt("Integer overflow on exponentiation of two constants"),
            }
        } else {
            let mut result = Self::one();

            // TODO (@pranav) In each step, we check that we have not overflowed,
            //  yet we know that in the first step, we do not need to check and
            //  in general we do not need to check for overflow until we have found
            //  the second bit that has been set. Optimize.
            // TODO (@pranav) Is there a constraint advantage in using the square operation
            //   in the field?
            for bit in other.bits_le.iter().rev() {
                result = (&result).mul_checked(&result);
                // TODO (@pranav) Confirm that this mul_checked won't always fail.
                //  We want the overflow constraint to only fail if the bit is set.
                result = Self::ternary(&bit, &result.mul_checked(&self), &result);
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

    use rand::thread_rng;

    const ITERATIONS: usize = 128;

    #[rustfmt::skip]
    fn check_pow_checked<I: IntegerType>(
        name: &str,
        expected: I,
        a: &Integer<Circuit, I>,
        b: &Integer<Circuit, u32>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, || {
            let case = format!("({} ** {})", a.eject_value(), b.eject_value());

            let candidate = a.pow_checked(b);
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := {}",
                expected,
                candidate.eject_value(),
                case
            );

            print!("Constants: {:?}, ", Circuit::num_constants_in_scope());
            print!("Public: {:?}, ", Circuit::num_public_in_scope());
            print!("Private: {:?}, ", Circuit::num_private_in_scope());
            print!("Constraints: {:?}\n", Circuit::num_constraints_in_scope());

            // assert_eq!(num_constants, Circuit::num_constants_in_scope(), "{} (num_constants)", case);
            // assert_eq!(num_public, Circuit::num_public_in_scope(), "{} (num_public)", case);
            // assert_eq!(num_private, Circuit::num_private_in_scope(), "{} (num_private)", case);
            // assert_eq!(num_constraints, Circuit::num_constraints_in_scope(), "{} (num_constraints)", case);
            assert!(Circuit::is_satisfied(), "{} (is_satisfied)", case);
        });
        Circuit::reset()
    }

    #[rustfmt::skip]
    fn check_overflow_halts<I: IntegerType + std::panic::RefUnwindSafe>(mode_a: Mode, mode_b: Mode, value_a: I, value_b: u32) {
        let a = Integer::<Circuit, I>::new(mode_a, value_a);
        let b = Integer::new(mode_b, value_b);
        let result = std::panic::catch_unwind(|| a.pow_checked(&b));
        assert!(result.is_err());
    }

    #[rustfmt::skip]
    fn check_overflow_fails<I: IntegerType + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        value_a: I,
        value_b: u32,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize
    ) {
        {
            let name = format!("Pow: {} ** {} overflows", value_a, value_b);
            let a = Integer::<Circuit, I>::new(mode_a, value_a);
            let b = Integer::new(mode_b, value_b);
            Circuit::scoped(&name, || {
                let case = format!("({} ** {})", a.eject_value(), b.eject_value());
                let _candidate = a.pow_checked(&b);

                print!("Constants: {:?}, ", Circuit::num_constants_in_scope());
                print!("Public: {:?}, ", Circuit::num_public_in_scope());
                print!("Private: {:?}, ", Circuit::num_private_in_scope());
                print!("Constraints: {:?}\n", Circuit::num_constraints_in_scope());

                // assert_eq!(num_constants, Circuit::num_constants_in_scope(), "{} (num_constants)", case);
                // assert_eq!(num_public, Circuit::num_public_in_scope(), "{} (num_public)", case);
                // assert_eq!(num_private, Circuit::num_private_in_scope(), "{} (num_private)", case);
                // assert_eq!(num_constraints, Circuit::num_constraints_in_scope(), "{} (num_constraints)", case);
                assert!(!Circuit::is_satisfied(), "{} (!is_satisfied)", case);
            });
            Circuit::reset()
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
            (_,_) => check_overflow_fails::<I>(mode_a, mode_b, value_a, value_b, num_constants, num_public, num_private, num_constraints),
        };

        for i in 0..ITERATIONS {
            let name = format!("Pow: {} ** {} {}", mode_a, mode_b, i);
            // TODO (@pranav) Uniform random sampling almost always produces arguments that result in an overflow.
            //  Is there a better method for sampling arguments?
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: u32 = UniformRand::rand(&mut thread_rng());

            let a = Integer::<Circuit, I>::new(mode_a, first);
            let b = Integer::new(mode_b, second);

            match first.checked_pow(second) {
                Some(expected) => check_pow_checked::<I>(&name, expected, &a, &b, num_constants, num_public, num_private, num_constraints),
                None => check_overflow(first, second),
            }
        }

        // let check_case = |expected: I, first: I, second: I| {
        //     let name = format!("Pow: {} ** {}", mode_a, mode_b);
        //     let a = Integer::<Circuit, I>::new(mode_a, first);
        //     let b = Integer::new(mode_b, second);
        //     check_pow_checked::<I, Integer<Circuit, I>>(&name, expected, &a, &b, num_constants, num_public, num_private, num_constraints)
        // };

        // // Check specific cases common to signed and unsigned integers.
        // check_case(I::MAX, I::one(), I::MAX);
        // check_case(I::MAX, I::MAX, I::one());
        // check_case(I::MIN, I::one(), I::MIN);
        // check_case(I::MIN, I::MIN, I::one());
        // check_case(I::zero(), I::zero(), I::MAX);
        // check_case(I::zero(), I::MAX, I::zero());
        // check_case(I::zero(), I::zero(), I::MIN);
        // check_case(I::zero(), I::MIN, I::zero());
        // check_case(I::one(), I::one(), I::one());
        //
        // // Check common overflow cases.
        // check_overflow(I::MAX, I::one() + I::one());
        // check_overflow(I::one() + I::one(), I::MAX);
        //
        // // Check additional corner cases for signed integers.
        // if I::is_signed() {
        //     check_case(I::MIN + I::one(), I::MAX, I::zero() - I::one());
        //     check_case(I::MIN + I::one(), I::zero() - I::one(), I::MAX);
        //
        //     check_overflow(I::MIN, I::zero() - I::one());
        //     check_overflow(I::zero() - I::one(), I::MIN);
        //     check_overflow(I::MIN, I::zero() - I::one() - I::one());
        //     check_overflow(I::zero() - I::one() - I::one(), I::MIN);
        // }
    }

    #[test]
    fn test_u8_constant_pow_constant() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_pow_public() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Public, 3, 0, 26, 28);
    }

    #[test]
    fn test_u8_constant_pow_private() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Private, 3, 0, 26, 28);
    }

    #[test]
    fn test_u8_public_pow_constant() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Constant, 3, 0, 26, 28);
    }

    #[test]
    fn test_u8_private_pow_constant() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Constant, 3, 0, 26, 28);
    }

    #[test]
    fn test_u8_public_pow_public() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Public, 3, 0, 26, 28);
    }

    #[test]
    fn test_u8_public_pow_private() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Private, 3, 0, 26, 28);
    }

    #[test]
    fn test_u8_private_pow_public() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Public, 3, 0, 26, 28);
    }

    #[test]
    fn test_u8_private_pow_private() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Private, 3, 0, 26, 28);
    }

    // Tests for i8

    #[test]
    fn test_i8_constant_pow_constant() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_pow_public() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Public, 40, 0, 76, 80);
    }

    #[test]
    fn test_i8_constant_pow_private() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Private, 40, 0, 76, 80);
    }

    #[test]
    fn test_i8_public_pow_constant() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Constant, 40, 0, 76, 80);
    }

    #[test]
    fn test_i8_private_pow_constant() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Constant, 40, 0, 76, 80);
    }

    #[test]
    fn test_i8_public_pow_public() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Public, 34, 0, 96, 101);
    }

    #[test]
    fn test_i8_public_pow_private() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Private, 34, 0, 96, 101);
    }

    #[test]
    fn test_i8_private_pow_public() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Public, 34, 0, 96, 101);
    }

    #[test]
    fn test_i8_private_pow_private() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Private, 34, 0, 96, 101);
    }

    // Tests for u16

    #[test]
    fn test_u16_constant_pow_constant() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_pow_public() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Public, 3, 0, 50, 52);
    }

    #[test]
    fn test_u16_constant_pow_private() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Private, 3, 0, 50, 52);
    }

    #[test]
    fn test_u16_public_pow_constant() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Constant, 3, 0, 50, 52);
    }

    #[test]
    fn test_u16_private_pow_constant() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Constant, 3, 0, 50, 52);
    }

    #[test]
    fn test_u16_public_pow_public() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Public, 3, 0, 50, 52);
    }

    #[test]
    fn test_u16_public_pow_private() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Private, 3, 0, 50, 52);
    }

    #[test]
    fn test_u16_private_pow_public() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Public, 3, 0, 50, 52);
    }

    #[test]
    fn test_u16_private_pow_private() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Private, 3, 0, 50, 52);
    }

    // Tests for i16

    #[test]
    fn test_i16_constant_pow_constant() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_pow_public() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Public, 72, 0, 140, 144);
    }

    #[test]
    fn test_i16_constant_pow_private() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Private, 72, 0, 140, 144);
    }

    #[test]
    fn test_i16_public_pow_constant() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Constant, 72, 0, 140, 144);
    }

    #[test]
    fn test_i16_private_pow_constant() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Constant, 72, 0, 140, 144);
    }

    #[test]
    fn test_i16_public_pow_public() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Public, 58, 0, 176, 181);
    }

    #[test]
    fn test_i16_public_pow_private() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Private, 58, 0, 176, 181);
    }

    #[test]
    fn test_i16_private_pow_public() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Public, 58, 0, 176, 181);
    }

    #[test]
    fn test_i16_private_pow_private() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Private, 58, 0, 176, 181);
    }

    // Tests for u32

    #[test]
    fn test_u32_constant_pow_constant() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_pow_public() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Public, 3, 0, 98, 100);
    }

    #[test]
    fn test_u32_constant_pow_private() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Private, 3, 0, 98, 100);
    }

    #[test]
    fn test_u32_public_pow_constant() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Constant, 3, 0, 98, 100);
    }

    #[test]
    fn test_u32_private_pow_constant() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Constant, 3, 0, 98, 100);
    }

    #[test]
    fn test_u32_public_pow_public() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Public, 3, 0, 98, 100);
    }

    #[test]
    fn test_u32_public_pow_private() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Private, 3, 0, 98, 100);
    }

    #[test]
    fn test_u32_private_pow_public() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Public, 3, 0, 98, 100);
    }

    #[test]
    fn test_u32_private_pow_private() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Private, 3, 0, 98, 100);
    }

    // Tests for i32

    #[test]
    fn test_i32_constant_pow_constant() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_pow_public() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Public, 136, 0, 268, 272);
    }

    #[test]
    fn test_i32_constant_pow_private() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Private, 136, 0, 268, 272)
    }

    #[test]
    fn test_i32_public_pow_constant() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Constant, 136, 0, 268, 272);
    }

    #[test]
    fn test_i32_private_pow_constant() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Constant, 136, 0, 268, 272);
    }

    #[test]
    fn test_i32_public_pow_public() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Public, 106, 0, 336, 341);
    }

    #[test]
    fn test_i32_public_pow_private() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Private, 106, 0, 336, 341);
    }

    #[test]
    fn test_i32_private_pow_public() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public, 106, 0, 336, 341);
    }

    #[test]
    fn test_i32_private_pow_private() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Private, 106, 0, 336, 341);
    }

    // Tests for u64

    #[test]
    fn test_u64_constant_pow_constant() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_pow_public() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Public, 3, 0, 194, 196);
    }

    #[test]
    fn test_u64_constant_pow_private() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Private, 3, 0, 194, 196);
    }

    #[test]
    fn test_u64_public_pow_constant() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Constant, 3, 0, 194, 196);
    }

    #[test]
    fn test_u64_private_pow_constant() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Constant, 3, 0, 194, 196);
    }

    #[test]
    fn test_u64_public_pow_public() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Public, 3, 0, 194, 196);
    }

    #[test]
    fn test_u64_public_pow_private() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Private, 3, 0, 194, 196);
    }

    #[test]
    fn test_u64_private_pow_public() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Public, 3, 0, 194, 196);
    }

    #[test]
    fn test_u64_private_pow_private() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Private, 3, 0, 194, 196);
    }

    // Tests for i64

    #[test]
    fn test_i64_constant_pow_constant() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_pow_public() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Public, 264, 0, 524, 528);
    }

    #[test]
    fn test_i64_constant_pow_private() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Private, 264, 0, 524, 528);
    }

    #[test]
    fn test_i64_public_pow_constant() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Constant, 264, 0, 524, 528);
    }

    #[test]
    fn test_i64_private_pow_constant() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Constant, 264, 0, 524, 528);
    }

    #[test]
    fn test_i64_public_pow_public() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Public, 202, 0, 656, 661);
    }

    #[test]
    fn test_i64_public_pow_private() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Private, 202, 0, 656, 661);
    }

    #[test]
    fn test_i64_private_pow_public() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Public, 202, 0, 656, 661);
    }

    #[test]
    fn test_i64_private_pow_private() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Private, 202, 0, 656, 661);
    }

    // Tests for u128

    #[test]
    fn test_u128_constant_pow_constant() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_pow_public() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Public, 9, 0, 521, 524);
    }

    #[test]
    fn test_u128_constant_pow_private() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Private, 9, 0, 521, 524);
    }

    #[test]
    fn test_u128_public_pow_constant() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Constant, 9, 0, 521, 524);
    }

    #[test]
    fn test_u128_private_pow_constant() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Constant, 9, 0, 521, 524);
    }

    #[test]
    fn test_u128_public_pow_public() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Public, 9, 0, 521, 524);
    }

    #[test]
    fn test_u128_public_pow_private() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Private, 9, 0, 521, 524);
    }

    #[test]
    fn test_u128_private_pow_public() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Public, 9, 0, 521, 524);
    }

    #[test]
    fn test_u128_private_pow_private() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Private, 9, 0, 521, 524);
    }

    // Tests for i128

    #[test]
    fn test_i128_constant_pow_constant() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_pow_public() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Public, 526, 0, 1171, 1176);
    }

    #[test]
    fn test_i128_constant_pow_private() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Private, 526, 0, 1171, 1176);
    }

    #[test]
    fn test_i128_public_pow_constant() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Constant, 526, 0, 1171, 1176);
    }

    #[test]
    fn test_i128_private_pow_constant() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Constant, 526, 0, 1171, 1176);
    }

    #[test]
    fn test_i128_public_pow_public() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Public, 400, 0, 1431, 1437);
    }

    #[test]
    fn test_i128_public_pow_private() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Private, 400, 0, 1431, 1437);
    }

    #[test]
    fn test_i128_private_pow_public() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Public, 400, 0, 1431, 1437);
    }

    #[test]
    fn test_i128_private_pow_private() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Private, 400, 0, 1431, 1437);
    }
}
