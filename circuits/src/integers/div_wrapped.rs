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

impl<E: Environment, I: IntegerType> DivWrapped<Self> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn div_wrapped(&self, other: &Integer<E, I>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the quotient and return the new constant.
            match other.eject_value() {
                value if value == I::zero() => E::halt("Division by zero error on division of two constants"),
                _ => Integer::new(Mode::Constant, self.eject_value().wrapping_div(&other.eject_value())),
            }
        } else {
            if I::is_signed() {
                todo!()
            } else {
                let bits_le = Self::divide_bits_in_field(&self.bits_le, &other.bits_le);

                // Return the difference of `self` and `other`.
                Integer { bits_le, phantom: Default::default() }
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

    use num_traits::{One};
    use rand::thread_rng;

    const ITERATIONS: usize = 128;

    fn check_div_wrapped<I: IntegerType, IC: IntegerTrait<I>>(
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
            let case = format!("({} / {})", a.eject_value(), b.eject_value());

            let candidate = a.div_wrapped(b);
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

            assert_eq!(num_constants, Circuit::num_constants_in_scope(), "{} (num_constants)", case);
            assert_eq!(num_public, Circuit::num_public_in_scope(), "{} (num_public)", case);
            assert_eq!(num_private, Circuit::num_private_in_scope(), "{} (num_private)", case);
            assert_eq!(num_constraints, Circuit::num_constraints_in_scope(), "{} (num_constraints)", case);
            assert!(Circuit::is_satisfied(), "{} (is_satisfied)", case);
        });
        Circuit::reset();
    }

    #[rustfmt::skip]
    fn check_division_by_zero_halts<I: IntegerType + std::panic::RefUnwindSafe>(mode_a: Mode, mode_b: Mode, value_a: I, value_b: I) {
        let a = Integer::<Circuit, I>::new(mode_a, value_a);
        let b = Integer::new(mode_b, value_b);
        let result = std::panic::catch_unwind(|| a.div_checked(&b));
        assert!(result.is_err());
    }

    #[rustfmt::skip]
    fn check_division_by_zero_fails<I: IntegerType + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        value_a: I,
        value_b: I,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize
    ) {
        let name = format!("Division By Zero: {} / {}", value_a, value_b);
        let a = Integer::<Circuit, I>::new(mode_a, value_a);
        let b = Integer::new(mode_b, value_b);
        Circuit::scoped(&name, || {
            let case = format!("({} / {})", a.eject_value(), b.eject_value());
            let _candidate = a.div_wrapped(&b);


            assert_eq!(num_constants, Circuit::num_constants_in_scope(), "{} (num_constants)", case);
            assert_eq!(num_public, Circuit::num_public_in_scope(), "{} (num_public)", case);
            assert_eq!(num_private, Circuit::num_private_in_scope(), "{} (num_private)", case);
            assert_eq!(num_constraints, Circuit::num_constraints_in_scope(), "{} (num_constraints)", case);
            assert!(!Circuit::is_satisfied(), "{} (!is_satisfied)", case);
        });
        Circuit::reset();
    }

    fn run_test<I: IntegerType + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        // Select the appropriate division by zero check based on modes of the input.
        let check_division_by_zero = |mode_a, mode_b, first, second| {
            match (mode_a, mode_b) {
                (Mode::Constant, Mode::Constant) => check_division_by_zero_halts(mode_a, mode_b, first, second),
                _ => check_division_by_zero_fails(mode_a, mode_b, first, second, num_constants, num_public, num_private, num_constraints),
            }
        };

        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: I = UniformRand::rand(&mut thread_rng());

            match (first, second) {
                (_, divisor) if divisor == I::zero() => check_division_by_zero(mode_a, mode_b, first, second),
                _ => {
                    let expected = first.wrapping_div(&second);
                    let a = Integer::<Circuit, I>::new(mode_a, first);
                    let b = Integer::new(mode_b, second);

                    let name = format!("Div: a / b {}", i);
                    check_div_wrapped::<I, Integer<Circuit, I>>(&name, expected, &a, &b, num_constants, num_public, num_private, num_constraints);
                }
            }
        }
    }

    #[test]
    fn test_u8_constant_div_constant() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_div_public() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Public, 6, 0, 83, 93);
    }

    #[test]
    fn test_u8_constant_div_private() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Private, 6, 0, 83, 93);
    }

    #[test]
    fn test_u8_public_div_constant() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Constant, 6, 0, 83, 93);
    }

    #[test]
    fn test_u8_private_div_constant() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Constant, 6, 0, 83, 93);
    }

    #[test]
    fn test_u8_public_div_public() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Public, 6, 0, 83, 93);
    }

    #[test]
    fn test_u8_public_div_private() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Private, 6, 0, 83, 93);
    }

    #[test]
    fn test_u8_private_div_public() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Public, 6, 0, 83, 93);
    }

    #[test]
    fn test_u8_private_div_private() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Private, 6, 0, 83, 93);
    }

    // Tests for i8

    #[test]
    fn test_i8_constant_div_constant() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_div_public() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Public, 6, 0, 83, 93);
    }

    #[test]
    fn test_i8_constant_div_private() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Private, 6, 0, 83, 93);
    }

    #[test]
    fn test_i8_public_div_constant() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Constant, 6, 0, 83, 93);
    }

    #[test]
    fn test_i8_private_div_constant() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Constant, 6, 0, 83, 93);
    }

    #[test]
    fn test_i8_public_div_public() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Public, 6, 0, 83, 93);
    }

    #[test]
    fn test_i8_public_div_private() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Private, 6, 0, 83, 93);
    }

    #[test]
    fn test_i8_private_div_public() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Public, 6, 0, 83, 93);
    }

    #[test]
    fn test_i8_private_div_private() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Private, 6, 0, 83, 93);
    }

    // Tests for u16

    #[test]
    fn test_u16_constant_div_constant() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_div_public() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Public, 6, 0, 291, 309);
    }

    #[test]
    fn test_u16_constant_div_private() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Private, 6, 0, 291, 309);
    }

    #[test]
    fn test_u16_public_div_constant() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Constant, 6, 0, 291, 309);
    }

    #[test]
    fn test_u16_private_div_constant() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Constant, 6, 0, 291, 309);
    }

    #[test]
    fn test_u16_public_div_public() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Public, 6, 0, 291, 309);
    }

    #[test]
    fn test_u16_public_div_private() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Private, 6, 0, 291, 309);
    }

    #[test]
    fn test_u16_private_div_public() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Public, 6, 0, 291, 309);
    }

    #[test]
    fn test_u16_private_div_private() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Private, 6, 0, 291, 309);
    }

    // Tests for i16

    #[test]
    fn test_i16_constant_div_constant() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_div_public() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Public, 6, 0, 291, 309);
    }

    #[test]
    fn test_i16_constant_div_private() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Private, 6, 0, 291, 309);
    }

    #[test]
    fn test_i16_public_div_constant() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Constant, 6, 0, 291, 309);
    }

    #[test]
    fn test_i16_private_div_constant() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Constant, 6, 0, 291, 309);
    }

    #[test]
    fn test_i16_public_div_public() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Public, 6, 0, 291, 309);
    }

    #[test]
    fn test_i16_public_div_private() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Private, 6, 0, 291, 309);
    }

    #[test]
    fn test_i16_private_div_public() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Public, 6, 0, 291, 309);
    }

    #[test]
    fn test_i16_private_div_private() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Private, 6, 0, 291, 309);
    }

    // Tests for u32

    #[test]
    fn test_u32_constant_div_constant() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_div_public() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Public, 6, 0, 1091, 1125);
    }

    #[test]
    fn test_u32_constant_div_private() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Private, 6, 0, 1091, 1125);
    }

    #[test]
    fn test_u32_public_div_constant() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Constant, 6, 0, 1091, 1125);
    }

    #[test]
    fn test_u32_private_div_constant() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Constant, 6, 0, 1091, 1125);
    }

    #[test]
    fn test_u32_public_div_public() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Public, 6, 0, 1091, 1125);
    }

    #[test]
    fn test_u32_public_div_private() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Private, 6, 0, 1091, 1125);
    }

    #[test]
    fn test_u32_private_div_public() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Public, 6, 0, 1091, 1125);
    }

    #[test]
    fn test_u32_private_div_private() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Private, 6, 0, 1091, 1125);
    }

    // Tests for i32

    #[test]
    fn test_i32_constant_div_constant() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_div_public() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Public, 6, 0, 1091, 1125);
    }

    #[test]
    fn test_i32_constant_div_private() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Private, 6, 0, 1091, 1125);
    }

    #[test]
    fn test_i32_public_div_constant() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Constant, 6, 0, 1091, 1125);
    }

    #[test]
    fn test_i32_private_div_constant() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Private, 6, 0, 1091, 1125);
    }

    #[test]
    fn test_i32_public_div_public() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Public, 6, 0, 1091, 1125);
    }

    #[test]
    fn test_i32_public_div_private() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Private, 6, 0, 1091, 1125);
    }

    #[test]
    fn test_i32_private_div_public() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public, 6, 0, 1091, 1125);
    }

    #[test]
    fn test_i32_private_div_private() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Private, 6, 0, 1091, 1125);
    }

    // Tests for u64

    #[test]
    fn test_u64_constant_div_constant() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_div_public() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Public, 6, 0, 4227, 4293);
    }

    #[test]
    fn test_u64_constant_div_private() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Private, 6, 0, 4227, 4293);
    }

    #[test]
    fn test_u64_public_div_constant() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Constant, 6, 0, 4227, 4293);
    }

    #[test]
    fn test_u64_private_div_constant() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Constant, 6, 0, 4227, 4293);
    }

    #[test]
    fn test_u64_public_div_public() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Public, 6, 0, 4227, 4293);
    }

    #[test]
    fn test_u64_public_div_private() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Private, 6, 0, 4227, 4293);
    }

    #[test]
    fn test_u64_private_div_public() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Public, 6, 0, 4227, 4293);
    }

    #[test]
    fn test_u64_private_div_private() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Private, 6, 0, 4227, 4293);
    }

    // Tests for i64

    #[test]
    fn test_i64_constant_div_constant() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_div_public() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Public, 6, 0, 4227, 4293);
    }

    #[test]
    fn test_i64_constant_div_private() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Private, 6, 0, 4227, 4293);
    }

    #[test]
    fn test_i64_public_div_constant() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Constant, 6, 0, 4227, 4293);
    }

    #[test]
    fn test_i64_private_div_constant() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Constant, 6, 0, 4227, 4293);
    }

    #[test]
    fn test_i64_public_div_public() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Public, 6, 0, 4227, 4293);
    }

    #[test]
    fn test_i64_public_div_private() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Private, 6, 0, 4227, 4293);
    }

    #[test]
    fn test_i64_private_div_public() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Public, 6, 0, 4227, 4293);
    }

    #[test]
    fn test_i64_private_div_private() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Private, 6, 0, 4227, 4293);
    }

    // Tests for u128

    #[test]
    fn test_u128_constant_div_constant() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_div_public() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Public, 6, 0, 16643, 16773);
    }

    #[test]
    fn test_u128_constant_div_private() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Private, 6, 0, 16643, 16773);
    }

    #[test]
    fn test_u128_public_div_constant() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Constant, 6, 0, 16643, 16773);
    }

    #[test]
    fn test_u128_private_div_constant() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Constant, 6, 0, 16643, 16773);
    }

    #[test]
    fn test_u128_public_div_public() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Public, 6, 0, 16643, 16773);
    }

    #[test]
    fn test_u128_public_div_private() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Private, 6, 0, 16643, 16773);
    }

    #[test]
    fn test_u128_private_div_public() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Public, 6, 0, 16643, 16773);
    }

    #[test]
    fn test_u128_private_div_private() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Private, 6, 0, 16643, 16773);
    }

    // Tests for i128

    #[test]
    fn test_i128_constant_div_constant() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_div_public() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Public, 6, 0, 16643, 16773);
    }

    #[test]
    fn test_i128_constant_div_private() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Private, 6, 0, 16643, 16773);
    }

    #[test]
    fn test_i128_public_div_constant() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Constant, 6, 0, 16643, 16773);
    }

    #[test]
    fn test_i128_private_div_constant() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Constant, 6, 0, 16643, 16773);
    }

    #[test]
    fn test_i128_public_div_public() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Public, 6, 0, 16643, 16773);
    }

    #[test]
    fn test_i128_public_div_private() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Private, 6, 0, 16643, 16773);
    }

    #[test]
    fn test_i128_private_div_public() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Public, 6, 0, 16643, 16773);
    }

    #[test]
    fn test_i128_private_div_private() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Private, 6, 0, 16643, 16773);
    }
}
