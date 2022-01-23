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
            match I::is_signed() {
                true => {
                    // Return `self` + -(`other`).
                    self.add_checked(&-other)
                }
                false => {
                    // Negate each bit in the representation of the `other` integer.
                    let neg_other = Integer::from_bits(other.bits_le.iter().map(|b| !b).collect());
                    // Return `self` + -(`other`).
                    self.add_checked(&neg_other.add_wrapped(&Integer::one()))
                }
            }
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
        Circuit::scoped(name, |scope| {
            let case = format!("({} - {})", a.eject_value(), b.eject_value());

            let candidate = a.sub_checked(b);
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := {}",
                expected,
                candidate.eject_value(),
                case
            );

            // assert_eq!(num_constants, scope.num_constants_in_scope(), "{} (num_constants)", case);
            // assert_eq!(num_public, scope.num_public_in_scope(), "{} (num_public)", case);
            // assert_eq!(num_private, scope.num_private_in_scope(), "{} (num_private)", case);
            // assert_eq!(num_constraints, scope.num_constraints_in_scope(), "{} (num_constraints)", case);
            assert!(Circuit::is_satisfied(), "{} (is_satisfied)", case);
        });
    }

    #[rustfmt::skip]
    fn check_underflow_halts<I: IntegerType + std::panic::RefUnwindSafe>(mode_a: Mode, mode_b: Mode) {
        let a = Integer::<Circuit, I>::new(mode_a, I::MIN);
        let b = Integer::new(mode_b, I::one());
        let result = std::panic::catch_unwind(|| a.sub_checked(&b));
        assert!(result.is_err());
    }

    #[rustfmt::skip]
    fn check_underflow_fails<I: IntegerType + std::panic::RefUnwindSafe>(mode_a: Mode, mode_b: Mode) {
        let name = format!("Sub: {} - {} underflows", I::MIN, I::one());
        let a = Integer::<Circuit, I>::new(mode_a, I::MIN);
        let b = Integer::new(mode_b, I::one());
        Circuit::scoped(&name, |_| {
            let case = format!("({} - {})", a.eject_value(), b.eject_value());
            let _candidate = a.sub_checked(&b);
            assert!(!Circuit::is_satisfied(), "{} (!is_satisfied)", case);
        });
    }

    #[rustfmt::skip]
    fn run_test<I: IntegerType>(
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
            let expected = match first.checked_sub(&second) {
                Some(value) => value,
                None => continue,
            };

            let a = Integer::<Circuit, I>::new(mode_a, first);
            let b = Integer::new(mode_b, second);

            let name = format!("Sub: a - b {}", i);
            check_sub_checked::<I, Integer<Circuit, I>>(&name, expected, &a, &b, num_constants, num_public, num_private, num_constraints);
        }
    }

    #[test]
    fn test_u8_constant_minus_constant() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
        check_underflow_halts::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_u8_constant_minus_public() {
        type I = u8;
        check_underflow_fails::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u8_constant_minus_private() {
        type I = u8;
        check_underflow_fails::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u8_public_minus_constant() {
        type I = u8;
        check_underflow_fails::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u8_private_minus_constant() {
        type I = u8;
        check_underflow_fails::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u8_public_minus_public() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Public, 10, 0, 50, 51);
        check_underflow_fails::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u8_public_minus_private() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Private, 10, 0, 50, 51);
        check_underflow_fails::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u8_private_minus_public() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Public, 10, 0, 50, 51);
        check_underflow_fails::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u8_private_minus_private() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Private, 10, 0, 50, 51);
        check_underflow_fails::<I>(Mode::Private, Mode::Private);
    }

    // Tests for i8

    #[test]
    fn test_i8_constant_minus_constant() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
        check_underflow_halts::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i8_constant_minus_public() {
        type I = i8;
        check_underflow_fails::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i8_constant_minus_private() {
        type I = i8;
        check_underflow_fails::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i8_public_minus_constant() {
        type I = i8;
        check_underflow_fails::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i8_private_minus_constant() {
        type I = i8;
        check_underflow_fails::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i8_public_minus_public() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Public, 10, 0, 51, 52);
        check_underflow_fails::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i8_public_minus_private() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Private, 10, 0, 51, 52);
        check_underflow_fails::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i8_private_minus_public() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Public, 10, 0, 51, 52);
        check_underflow_fails::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i8_private_minus_private() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Private, 10, 0, 51, 52);
        check_underflow_fails::<I>(Mode::Private, Mode::Private);
    }

    // Tests for u16

    #[test]
    fn test_u16_constant_minus_constant() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
        check_underflow_halts::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_u16_constant_minus_public() {
        type I = u16;
        check_underflow_fails::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u16_constant_minus_private() {
        type I = u16;
        check_underflow_fails::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u16_public_minus_constant() {
        type I = u16;
        check_underflow_fails::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u16_private_minus_constant() {
        type I = u16;
        check_underflow_fails::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u16_public_minus_public() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Public, 18, 0, 106, 107);
        check_underflow_fails::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u16_public_minus_private() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Private, 18, 0, 106, 107);
        check_underflow_fails::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u16_private_minus_public() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Public, 18, 0, 106, 107);
        check_underflow_fails::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u16_private_minus_private() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Private, 18, 0, 106, 107);
        check_underflow_fails::<I>(Mode::Private, Mode::Private);
    }

    // Tests for i16

    #[test]
    fn test_i16_constant_minus_constant() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
        check_underflow_halts::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i16_constant_minus_public() {
        type I = i16;
        check_underflow_fails::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i16_constant_minus_private() {
        type I = i16;
        check_underflow_fails::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i16_public_minus_constant() {
        type I = i16;
        check_underflow_fails::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i16_private_minus_constant() {
        type I = i16;
        check_underflow_fails::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i16_public_minus_public() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Public, 18, 0, 107, 108);
        check_underflow_fails::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i16_public_minus_private() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Private, 18, 0, 107, 108);
        check_underflow_fails::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i16_private_minus_public() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Public, 18, 0, 107, 108);
        check_underflow_fails::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i16_private_minus_private() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Private, 18, 0, 107, 108);
        check_underflow_fails::<I>(Mode::Private, Mode::Private);
    }

    // Tests for u32

    #[test]
    fn test_u32_constant_minus_constant() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
        check_underflow_halts::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_u32_constant_minus_public() {
        type I = u32;
        check_underflow_fails::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u32_constant_minus_private() {
        type I = u32;
        check_underflow_fails::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u32_public_minus_constant() {
        type I = u32;
        check_underflow_fails::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u32_private_minus_constant() {
        type I = u32;
        check_underflow_fails::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u32_public_minus_public() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Public, 34, 0, 218, 219);
        check_underflow_fails::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u32_public_minus_private() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Private, 34, 0, 218, 219);
        check_underflow_fails::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u32_private_minus_public() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Public, 34, 0, 218, 219);
        check_underflow_fails::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u32_private_minus_private() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Private, 34, 0, 218, 219);
        check_underflow_fails::<I>(Mode::Private, Mode::Private);
    }

    // Tests for i32

    #[test]
    fn test_i32_constant_minus_constant() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
        check_underflow_halts::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i32_constant_minus_public() {
        type I = i32;
        check_underflow_fails::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i32_constant_minus_private() {
        type I = i32;
        check_underflow_fails::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i32_public_minus_constant() {
        type I = i32;
        check_underflow_fails::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i32_private_minus_constant() {
        type I = i32;
        check_underflow_fails::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i32_public_minus_public() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Public, 34, 0, 219, 220);
        check_underflow_fails::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i32_public_minus_private() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Private, 34, 0, 219, 220);
        check_underflow_fails::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i32_private_minus_public() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public, 34, 0, 219, 220);
        check_underflow_fails::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i32_private_minus_private() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Private, 34, 0, 219, 220);
        check_underflow_fails::<I>(Mode::Private, Mode::Private);
    }

    // Tests for u64

    #[test]
    fn test_u64_constant_minus_constant() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
        check_underflow_halts::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_u64_constant_minus_public() {
        type I = u64;
        check_underflow_fails::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u64_constant_minus_private() {
        type I = u64;
        check_underflow_fails::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u64_public_minus_constant() {
        type I = u64;
        check_underflow_fails::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u64_private_minus_constant() {
        type I = u64;
        check_underflow_fails::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u64_public_minus_public() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Public, 66, 0, 442, 443);
        check_underflow_fails::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u64_public_minus_private() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Private, 66, 0, 442, 443);
        check_underflow_fails::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u64_private_minus_public() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Public, 66, 0, 442, 443);
        check_underflow_fails::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u64_private_minus_private() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Private, 66, 0, 442, 443);
        check_underflow_fails::<I>(Mode::Private, Mode::Private);
    }

    // Tests for i64

    #[test]
    fn test_i64_constant_minus_constant() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
        check_underflow_halts::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i64_constant_minus_public() {
        type I = i64;
        check_underflow_fails::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i64_constant_minus_private() {
        type I = i64;
        check_underflow_fails::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i64_public_minus_constant() {
        type I = i64;
        check_underflow_fails::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i64_private_minus_constant() {
        type I = i64;
        check_underflow_fails::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i64_public_minus_public() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Public, 66, 0, 443, 444);
        check_underflow_fails::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i64_public_minus_private() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Private, 66, 0, 443, 444);
        check_underflow_fails::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i64_private_minus_public() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Public, 66, 0, 443, 444);
        check_underflow_fails::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i64_private_minus_private() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Private, 66, 0, 443, 444);
        check_underflow_fails::<I>(Mode::Private, Mode::Private);
    }

    // Tests for u128

    #[test]
    fn test_u128_constant_minus_constant() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
        check_underflow_halts::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_u128_constant_minus_public() {
        type I = u128;
        check_underflow_fails::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u128_constant_minus_private() {
        type I = u128;
        check_underflow_fails::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u128_public_minus_constant() {
        type I = u128;
        check_underflow_fails::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u128_private_minus_constant() {
        type I = u128;
        check_underflow_fails::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u128_public_minus_public() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Public, 130, 0, 890, 891);
        check_underflow_fails::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_u128_public_minus_private() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Private, 130, 0, 890, 891);
        check_underflow_fails::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_u128_private_minus_public() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Public, 130, 0, 890, 891);
        check_underflow_fails::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_u128_private_minus_private() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Private, 130, 0, 890, 891);
        check_underflow_fails::<I>(Mode::Private, Mode::Private);
    }

    // Tests for i128

    #[test]
    fn test_i128_constant_minus_constant() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
        check_underflow_halts::<I>(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_i128_constant_minus_public() {
        type I = i128;
        check_underflow_fails::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i128_constant_minus_private() {
        type I = i128;
        check_underflow_fails::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i128_public_minus_constant() {
        type I = i128;
        check_underflow_fails::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i128_private_minus_constant() {
        type I = i128;
        check_underflow_fails::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i128_public_minus_public() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Public, 130, 0, 891, 892);
        check_underflow_fails::<I>(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_i128_public_minus_private() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Private, 130, 0, 891, 892);
        check_underflow_fails::<I>(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_i128_private_minus_public() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Public, 130, 0, 891, 892);
        check_underflow_fails::<I>(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_i128_private_minus_private() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Private, 130, 0, 891, 892);
        check_underflow_fails::<I>(Mode::Private, Mode::Private);
    }
}
