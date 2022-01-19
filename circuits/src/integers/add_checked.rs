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
use crate::helpers::Adder;

use itertools::Itertools;

impl<E: Environment, I: IntegerType> AddChecked<Self> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn add_checked(&self, other: &Integer<E, I>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the sum and return the new constant.
            match self.eject_value().checked_add(&other.eject_value()) {
                Some(value) => Integer::new(Mode::Constant, value),
                None => E::halt("Integer overflow on addition of two constants"),
            }
        } else {
            let mut bits_le = Vec::with_capacity(I::BITS);
            let mut carry = Boolean::new(Mode::Constant, false);

            // Perform a ripple-carry adder on the bits.
            for (a, b) in self.bits_le.iter().zip_eq(other.bits_le.iter()).take(I::BITS) {
                let (sum, next) = a.adder(b, &carry);
                carry = next;
                bits_le.push(sum);
            }

            // Ensure `carry` * 1 = 0.
            E::enforce(|| (carry, E::one(), E::zero()));

            // Stores the sum of `self` and `other` in `self`.
            Integer::from_bits(bits_le)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::{
        distributions::{Distribution, Standard},
        thread_rng,
    };

    const ITERATIONS: usize = 100;

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

            let candidate = a.add_checked(b);
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

    fn check_overflow_halts<I: IntegerType, IC: IntegerTrait<I> + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let a = IC::new(mode_a, I::MAX);
        let b = IC::new(mode_b, I::one());
        let result = std::panic::catch_unwind(|| a.add_checked(&b));
        assert!(result.is_err());

        let a = IC::new(mode_a, I::one());
        let b = IC::new(mode_b, I::MAX);
        let result = std::panic::catch_unwind(|| a.add_checked(&b));
        assert!(result.is_err());
    }

    fn check_overflow_fails<I: IntegerType, IC: IntegerTrait<I> + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
    ) {
        {
            let name = format!("Add: {} + {} overflows", I::MAX, I::one());
            let a = IC::new(mode_a, I::MAX);
            let b = IC::new(mode_b, I::one());
            Circuit::scoped(&name, |_| {
                let case = format!("({} + {})", a.eject_value(), b.eject_value());
                let _candidate = a.add_checked(&b);
                assert!(!Circuit::is_satisfied(), "{} (!is_satisfied)", case);
            });
        }
        {
            let name = format!("Add: {} + {} overflows", I::one(), I::MAX);
            let a = IC::new(mode_a, I::one());
            let b = IC::new(mode_b, I::MAX);
            Circuit::scoped(&name, |_| {
                let case = format!("({} + {})", a.eject_value(), b.eject_value());
                let _candidate = a.add_checked(&b);
                assert!(!Circuit::is_satisfied(), "{} (!is_satisfied)", case);
            });
        }
    }

    fn run_test<I: IntegerType, IC: IntegerTrait<I>>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) where
        Standard: Distribution<I>,
    {
        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: I = UniformRand::rand(&mut thread_rng());
            let expected = match first.checked_add(&second) {
                Some(value) => value,
                None => continue,
            };

            let a = IC::new(mode_a, first);
            let b = IC::new(mode_b, second);

            let name = format!("Add: a + b {}", i);
            check_add_checked::<I, IC>(
                &name,
                expected,
                &a,
                &b,
                num_constants,
                num_public,
                num_private,
                num_constraints,
            );
        }
    }

    #[test]
    fn test_u8_constant_plus_constant() {
        type I = u8;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
        check_overflow_halts::<I, IC>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_u8_constant_plus_public() {
        type I = u8;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u8_constant_plus_private() {
        type I = u8;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u8_public_plus_constant() {
        type I = u8;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u8_private_plus_constant() {
        type I = u8;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u8_public_plus_public() {
        type I = u8;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Public, 1, 0, 37, 75);
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u8_public_plus_private() {
        type I = u8;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Private, 1, 0, 37, 75);
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u8_private_plus_public() {
        type I = u8;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Public, 1, 0, 37, 75);
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u8_private_plus_private() {
        type I = u8;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Private, 1, 0, 37, 75);
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Private);
    }

    // Tests for i8

    #[test]
    fn test_i8_constant_plus_constant() {
        type I = i8;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
        check_overflow_halts::<I, IC>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i8_constant_plus_public() {
        type I = i8;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i8_constant_plus_private() {
        type I = i8;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i8_public_plus_constant() {
        type I = i8;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i8_private_plus_constant() {
        type I = i8;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i8_public_plus_public() {
        type I = i8;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Public, 1, 0, 37, 75);
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i8_public_plus_private() {
        type I = i8;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Private, 1, 0, 37, 75);
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i8_private_plus_public() {
        type I = i8;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Public, 1, 0, 37, 75);
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i8_private_plus_private() {
        type I = i8;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Private, 1, 0, 37, 75);
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Private);
    }

    // Tests for u16

    #[test]
    fn test_u16_constant_plus_constant() {
        type I = u16;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
        check_overflow_halts::<I, IC>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_u16_constant_plus_public() {
        type I = u16;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u16_constant_plus_private() {
        type I = u16;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u16_public_plus_constant() {
        type I = u16;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u16_private_plus_constant() {
        type I = u16;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u16_public_plus_public() {
        type I = u16;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Public, 1, 0, 77, 155);
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u16_public_plus_private() {
        type I = u16;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Private, 1, 0, 77, 155);
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u16_private_plus_public() {
        type I = u16;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Public, 1, 0, 77, 155);
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u16_private_plus_private() {
        type I = u16;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Private, 1, 0, 77, 155);
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Private);
    }

    // Tests for i16

    #[test]
    fn test_i16_constant_plus_constant() {
        type I = i16;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
        check_overflow_halts::<I, IC>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i16_constant_plus_public() {
        type I = i16;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i16_constant_plus_private() {
        type I = i16;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i16_public_plus_constant() {
        type I = i16;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i16_private_plus_constant() {
        type I = i16;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i16_public_plus_public() {
        type I = i16;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Public, 1, 0, 77, 155);
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i16_public_plus_private() {
        type I = i16;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Private, 1, 0, 77, 155);
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i16_private_plus_public() {
        type I = i16;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Public, 1, 0, 77, 155);
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i16_private_plus_private() {
        type I = i16;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Private, 1, 0, 77, 155);
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Private);
    }

    // Tests for u32

    #[test]
    fn test_u32_constant_plus_constant() {
        type I = u32;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
        check_overflow_halts::<I, IC>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_u32_constant_plus_public() {
        type I = u32;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u32_constant_plus_private() {
        type I = u32;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u32_public_plus_constant() {
        type I = u32;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u32_private_plus_constant() {
        type I = u32;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u32_public_plus_public() {
        type I = u32;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Public, 1, 0, 157, 315);
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u32_public_plus_private() {
        type I = u32;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Private, 1, 0, 157, 315);
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u32_private_plus_public() {
        type I = u32;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Public, 1, 0, 157, 315);
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u32_private_plus_private() {
        type I = u32;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Private, 1, 0, 157, 315);
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Private);
    }

    // Tests for i32

    #[test]
    fn test_i32_constant_plus_constant() {
        type I = i32;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
        check_overflow_halts::<I, IC>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i32_constant_plus_public() {
        type I = i32;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i32_constant_plus_private() {
        type I = i32;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i32_public_plus_constant() {
        type I = i32;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i32_private_plus_constant() {
        type I = i32;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i32_public_plus_public() {
        type I = i32;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Public, 1, 0, 157, 315);
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i32_public_plus_private() {
        type I = i32;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Private, 1, 0, 157, 315);
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i32_private_plus_public() {
        type I = i32;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Public, 1, 0, 157, 315);
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i32_private_plus_private() {
        type I = i32;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Private, 1, 0, 157, 315);
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Private);
    }

    // Tests for u64

    #[test]
    fn test_u64_constant_plus_constant() {
        type I = u64;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
        check_overflow_halts::<I, IC>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_u64_constant_plus_public() {
        type I = u64;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u64_constant_plus_private() {
        type I = u64;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u64_public_plus_constant() {
        type I = u64;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u64_private_plus_constant() {
        type I = u64;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u64_public_plus_public() {
        type I = u64;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Public, 1, 0, 317, 635);
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u64_public_plus_private() {
        type I = u64;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Private, 1, 0, 317, 635);
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u64_private_plus_public() {
        type I = u64;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Public, 1, 0, 317, 635);
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u64_private_plus_private() {
        type I = u64;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Private, 1, 0, 317, 635);
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Private);
    }

    // Tests for i64

    #[test]
    fn test_i64_constant_plus_constant() {
        type I = i64;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
        check_overflow_halts::<I, IC>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i64_constant_plus_public() {
        type I = i64;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i64_constant_plus_private() {
        type I = i64;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i64_public_plus_constant() {
        type I = i64;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i64_private_plus_constant() {
        type I = i64;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i64_public_plus_public() {
        type I = i64;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Public, 1, 0, 317, 635);
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i64_public_plus_private() {
        type I = i64;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Private, 1, 0, 317, 635);
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i64_private_plus_public() {
        type I = i64;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Public, 1, 0, 317, 635);
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i64_private_plus_private() {
        type I = i64;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Private, 1, 0, 317, 635);
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Private);
    }

    // Tests for u128

    #[test]
    fn test_u128_constant_plus_constant() {
        type I = u128;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
        check_overflow_halts::<I, IC>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_u128_constant_plus_public() {
        type I = u128;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u128_constant_plus_private() {
        type I = u128;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u128_public_plus_constant() {
        type I = u128;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u128_private_plus_constant() {
        type I = u128;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u128_public_plus_public() {
        type I = u128;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Public, 1, 0, 637, 1275);
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u128_public_plus_private() {
        type I = u128;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Private, 1, 0, 637, 1275);
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u128_private_plus_public() {
        type I = u128;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Public, 1, 0, 637, 1275);
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u128_private_plus_private() {
        type I = u128;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Private, 1, 0, 637, 1275);
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Private);
    }

    // Tests for i128

    #[test]
    fn test_i128_constant_plus_constant() {
        type I = i128;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
        check_overflow_halts::<I, IC>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i128_constant_plus_public() {
        type I = i128;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i128_constant_plus_private() {
        type I = i128;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i128_public_plus_constant() {
        type I = i128;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i128_private_plus_constant() {
        type I = i128;
        type IC = Integer<Circuit, I>;
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i128_public_plus_public() {
        type I = i128;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Public, 1, 0, 637, 1275);
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i128_public_plus_private() {
        type I = i128;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Public, Mode::Private, 1, 0, 637, 1275);
        check_overflow_fails::<I, IC>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i128_private_plus_public() {
        type I = i128;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Public, 1, 0, 637, 1275);
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i128_private_plus_private() {
        type I = i128;
        type IC = Integer<Circuit, I>;
        run_test::<I, IC>(Mode::Private, Mode::Private, 1, 0, 637, 1275);
        check_overflow_fails::<I, IC>(Mode::Private, Mode::Private);
    }
}
