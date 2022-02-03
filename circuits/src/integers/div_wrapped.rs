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
use num_traits::NumCast;
use snarkvm_utilities::{FromBytes, ToBytes};

impl<E: Environment, I: IntegerType> DivWrapped<Self> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn div_wrapped(&self, other: &Integer<E, I>) -> Self::Output {
        // Halt on division by zero as there is no sound way to perform
        // this operation.
        if other.eject_value() == I::zero() {
            E::halt("Division by zero error")
        }

        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the quotient and return the new constant.
            Integer::new(Mode::Constant, self.eject_value().wrapping_div(&other.eject_value()))
        } else {
            if I::is_signed() {
                // This is safe since I::BITS is always greater than 0.
                let dividend_msb = self.bits_le.last().unwrap();
                let divisor_msb = other.bits_le.last().unwrap();

                // Signed integer division wraps when the dividend is I::MIN
                // and when the divisor is -1.
                let min = Self::new(Mode::Constant, I::MIN);
                let neg_one = Self::new(Mode::Constant, I::zero() - I::one());
                let division_wraps = self.is_eq(&min).and(&other.is_eq(&neg_one));

                // Divide the absolute value of `self` and `other` in the base field.
                let dividend_unsigned_integer =
                    Self::ternary(dividend_msb, &(!self).add_wrapped(&Self::one()), self).cast_as_dual();
                let divisor_unsigned_integer =
                    Self::ternary(divisor_msb, &(!other).add_wrapped(&Self::one()), other).cast_as_dual();

                let dividend_unsigned_value = dividend_unsigned_integer.eject_value();
                let divisor_unsigned_value = divisor_unsigned_integer.eject_value();

                let quotient_unsigned_value = dividend_unsigned_value.wrapping_div(&divisor_unsigned_value);
                let remainder_unsigned_value = dividend_unsigned_value.wrapping_rem(&divisor_unsigned_value);

                let quotient_unsigned_integer = Integer::<E, I::Dual>::new(Mode::Private, quotient_unsigned_value);
                let remainder_unsigned_integer = Integer::<E, I::Dual>::new(Mode::Private, remainder_unsigned_value);

                let dividend_field = BaseField::from_bits_le(Mode::Private, &dividend_unsigned_integer.bits_le);
                let divisor_field = BaseField::from_bits_le(Mode::Private, &divisor_unsigned_integer.bits_le);
                let quotient_field = BaseField::from_bits_le(Mode::Private, &quotient_unsigned_integer.bits_le);
                let remainder_field = BaseField::from_bits_le(Mode::Private, &remainder_unsigned_integer.bits_le);

                E::assert_eq(dividend_field, quotient_field * divisor_field + remainder_field);

                // TODO (@pranav) Do we need to check that the quotient cannot exceed abs(I::MIN)?
                //  This is implicitly true since the dividend <= abs(I::MIN) and 0 <= quotient <= dividend.
                let quotient_integer = Self { bits_le: quotient_unsigned_integer.bits_le, phantom: Default::default() };
                let operands_same_sign = &dividend_msb.is_eq(divisor_msb);
                let signed_result = Self::ternary(
                    operands_same_sign,
                    &quotient_integer,
                    &(!&quotient_integer).add_wrapped(&Self::one()),
                );

                Self::ternary(&division_wraps, &min, &signed_result)
            } else {
                let dividend_value = self.eject_value();
                let divisor_value = other.eject_value();

                let quotient_value = dividend_value.wrapping_div(&divisor_value);
                let remainder_value = dividend_value.wrapping_rem(&divisor_value);

                let quotient_integer = Integer::new(Mode::Private, quotient_value);
                let remainder_integer = Integer::new(Mode::Private, remainder_value);

                let dividend_field = BaseField::from_bits_le(Mode::Private, &self.bits_le);
                let divisor_field = BaseField::from_bits_le(Mode::Private, &other.bits_le);
                let quotient_field = BaseField::from_bits_le(Mode::Private, &quotient_integer.bits_le);
                let remainder_field = BaseField::from_bits_le(Mode::Private, &remainder_integer.bits_le);

                E::assert_eq(dividend_field, quotient_field * divisor_field + remainder_field);

                // Return the quotient of `self` and `other`.
                quotient_integer
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

    use num_traits::{One, Signed};
    use rand::thread_rng;

    const ITERATIONS: usize = 1024;

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
        let result = std::panic::catch_unwind(|| a.div_wrapped(&b));
        assert!(result.is_err());
    }

    // Note that only signed division can overflow.
    fn run_overflow_and_halt_test<I: IntegerType + Signed + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for _i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: I = I::zero();

            check_division_by_zero_halts(mode_a, mode_b, first, second);
        }

        check_division_by_zero_halts(mode_a, mode_b, I::MAX, I::zero());
        check_division_by_zero_halts(mode_a, mode_b, I::MIN, I::zero());
        check_division_by_zero_halts(mode_a, mode_b, I::one(), I::zero());
        check_division_by_zero_halts(mode_a, mode_b, I::zero(), I::zero());

        // Check overflow case.
        let first = I::MIN;
        let second = I::zero() - I::one();

        let expected = first.wrapping_div(&second);
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::new(mode_b, second);
        let name = format!("Div Overflow: {} / {}", first, second);
        check_div_wrapped::<I, Integer<Circuit, I>>(&name, expected, &a, &b, num_constants, num_public, num_private, num_constraints);
    }

    fn run_test<I: IntegerType + std::panic::RefUnwindSafe>(
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

            match (first, second) {
                (_, divisor) if divisor == I::zero() => check_division_by_zero_halts(mode_a, mode_b, first, second),
                _ => {
                    let expected = first.wrapping_div(&second);
                    let a = Integer::<Circuit, I>::new(mode_a, first);
                    let b = Integer::new(mode_b, second);

                    let name = format!("Div: a / b {}", i);
                    check_div_wrapped::<I, Integer<Circuit, I>>(&name, expected, &a, &b, num_constants, num_public, num_private, num_constraints);
                }
            }
        }

        let check_div = |first, second, expected| {
            let a = Integer::<Circuit, I>::new(mode_a, first);
            let b = Integer::new(mode_b, second);

            let name = format!("Div: {} / {}", first, second);
            check_div_wrapped::<I, Integer<Circuit, I>>(&name, expected, &a, &b, num_constants, num_public, num_private, num_constraints);
        };

        // Check standard division properties and corner cases.
        check_div(I::MAX, I::one(), I::MAX);
        check_div(I::MIN, I::one(), I::MIN);
        check_div(I::one(), I::one(), I::one());
        check_div(I::zero(), I::one(), I::zero());
        check_division_by_zero_halts(mode_a, mode_b, I::MAX, I::zero());
        check_division_by_zero_halts(mode_a, mode_b, I::MIN, I::zero());
        check_division_by_zero_halts(mode_a, mode_b, I::one(), I::zero());
        check_division_by_zero_halts(mode_a, mode_b, I::zero(),I::zero());

        // Check some additional corner cases for signed integer division.
        if I::is_signed() {
            check_div(I::MAX, I::zero() - I::one(), I::MIN + I::one());
            check_div(I::MIN, I::zero() - I::one(), I::MIN);
            check_div(I::one(), I::zero() - I::one(), I::zero() - I::one());
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
        run_test::<I>(Mode::Constant, Mode::Private, 4, 0, 21, 22);
    }

    #[test]
    fn test_u8_constant_div_private() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Private, 4, 0, 21, 22);
    }

    #[test]
    fn test_u8_public_div_constant() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Constant, 4, 0, 21, 22);
    }

    #[test]
    fn test_u8_private_div_constant() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Constant, 4, 0, 21, 22);
    }

    #[test]
    fn test_u8_public_div_public() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Public, 4, 0, 21, 22);
    }

    #[test]
    fn test_u8_public_div_private() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Private, 4, 0, 21, 22);
    }

    #[test]
    fn test_u8_private_div_public() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Public, 4, 0, 21, 22);
    }

    #[test]
    fn test_u8_private_div_private() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Private, 4, 0, 21, 22);
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
        run_overflow_and_halt_test::<I>(Mode::Constant, Mode::Public, 59, 0, 71, 75);
    }

    #[test]
    fn test_i8_constant_div_private() {
        type I = i8;
        run_overflow_and_halt_test::<I>(Mode::Constant, Mode::Private, 59, 0, 71, 75);
    }

    #[test]
    fn test_i8_public_div_constant() {
        type I = i8;
        run_overflow_and_halt_test::<I>(Mode::Public, Mode::Constant, 59, 0, 71, 75);
    }

    #[test]
    fn test_i8_private_div_constant() {
        type I = i8;
        run_overflow_and_halt_test::<I>(Mode::Private, Mode::Constant, 59, 0, 71, 75);
    }

    #[test]
    fn test_i8_public_div_public() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Public, 54, 0, 96, 102);
    }

    #[test]
    fn test_i8_public_div_private() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Private, 54, 0, 96, 102);
    }

    #[test]
    fn test_i8_private_div_public() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Public, 54, 0, 96, 102);
    }

    #[test]
    fn test_i8_private_div_private() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Private, 54, 0, 96, 102);
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
        run_test::<I>(Mode::Constant, Mode::Public, 4, 0, 37, 38);
    }

    #[test]
    fn test_u16_constant_div_private() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Private, 4, 0, 37, 38);
    }

    #[test]
    fn test_u16_public_div_constant() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Constant, 4, 0, 37, 38);
    }

    #[test]
    fn test_u16_private_div_constant() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Constant, 4, 0, 37, 38);
    }

    #[test]
    fn test_u16_public_div_public() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Public, 4, 0, 37, 38);
    }

    #[test]
    fn test_u16_public_div_private() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Private, 4, 0, 37, 38);
    }

    #[test]
    fn test_u16_private_div_public() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Public, 4, 0, 37, 38);
    }

    #[test]
    fn test_u16_private_div_private() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Private, 4, 0, 37, 38);
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
        run_overflow_and_halt_test::<I>(Mode::Constant, Mode::Public, 107, 0, 127, 131);
    }

    #[test]
    fn test_i16_constant_div_private() {
        type I = i16;
        run_overflow_and_halt_test::<I>(Mode::Constant, Mode::Private, 107, 0, 127, 131);
    }

    #[test]
    fn test_i16_public_div_constant() {
        type I = i16;
        run_overflow_and_halt_test::<I>(Mode::Public, Mode::Constant, 107, 0, 127, 131);
    }

    #[test]
    fn test_i16_private_div_constant() {
        type I = i16;
        run_overflow_and_halt_test::<I>(Mode::Private, Mode::Constant, 107, 0, 127, 131);
    }

    #[test]
    fn test_i16_public_div_public() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Public, 94, 0, 168, 174);
    }

    #[test]
    fn test_i16_public_div_private() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Private, 94, 0, 168, 174);
    }

    #[test]
    fn test_i16_private_div_public() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Public, 94, 0, 168, 174);
    }

    #[test]
    fn test_i16_private_div_private() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Private, 94, 0, 168, 174);
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
        run_test::<I>(Mode::Constant, Mode::Public, 4, 0, 69, 70);
    }

    #[test]
    fn test_u32_constant_div_private() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Private, 4, 0, 69, 70);
    }

    #[test]
    fn test_u32_public_div_constant() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Constant, 4, 0, 69, 70);
    }

    #[test]
    fn test_u32_private_div_constant() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Constant, 4, 0, 69, 70);
    }

    #[test]
    fn test_u32_public_div_public() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Public, 4, 0, 69, 70);
    }

    #[test]
    fn test_u32_public_div_private() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Private, 4, 0, 69, 70);
    }

    #[test]
    fn test_u32_private_div_public() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Public, 4, 0, 69, 70);
    }

    #[test]
    fn test_u32_private_div_private() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Private, 4, 0, 69, 70);
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
        run_overflow_and_halt_test::<I>(Mode::Constant, Mode::Public, 203, 0, 239, 243);
    }

    #[test]
    fn test_i32_constant_div_private() {
        type I = i32;
        run_overflow_and_halt_test::<I>(Mode::Constant, Mode::Private, 203, 0, 239, 243);
    }

    #[test]
    fn test_i32_public_div_constant() {
        type I = i32;
        run_overflow_and_halt_test::<I>(Mode::Public, Mode::Constant, 203, 0, 239, 243);
    }

    #[test]
    fn test_i32_private_div_constant() {
        type I = i32;
        run_overflow_and_halt_test::<I>(Mode::Constant, Mode::Private, 203, 0, 239, 243);
    }

    #[test]
    fn test_i32_public_div_public() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Public, 174, 0, 312, 318);
    }

    #[test]
    fn test_i32_public_div_private() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Private, 174, 0, 312, 318);
    }

    #[test]
    fn test_i32_private_div_public() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public, 174, 0, 312, 318);
    }

    #[test]
    fn test_i32_private_div_private() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Private, 174, 0, 312, 318);
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
        run_test::<I>(Mode::Constant, Mode::Public, 4, 0, 133, 134);
    }

    #[test]
    fn test_u64_constant_div_private() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Private, 4, 0, 133, 134);
    }

    #[test]
    fn test_u64_public_div_constant() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Constant, 4, 0, 133, 134);
    }

    #[test]
    fn test_u64_private_div_constant() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Constant, 4, 0, 133, 134);
    }

    #[test]
    fn test_u64_public_div_public() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Public, 4, 0, 133, 134);
    }

    #[test]
    fn test_u64_public_div_private() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Private, 4, 0, 133, 134);
    }

    #[test]
    fn test_u64_private_div_public() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Public, 4, 0, 133, 134);
    }

    #[test]
    fn test_u64_private_div_private() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Private, 4, 0, 133, 134);
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
        run_overflow_and_halt_test::<I>(Mode::Constant, Mode::Public, 395, 0, 463, 467);
    }

    #[test]
    fn test_i64_constant_div_private() {
        type I = i64;
        run_overflow_and_halt_test::<I>(Mode::Constant, Mode::Private, 395, 0, 463, 467);
    }

    #[test]
    fn test_i64_public_div_constant() {
        type I = i64;
        run_overflow_and_halt_test::<I>(Mode::Public, Mode::Constant, 395, 0, 463, 467);
    }

    #[test]
    fn test_i64_private_div_constant() {
        type I = i64;
        run_overflow_and_halt_test::<I>(Mode::Private, Mode::Constant, 395, 0, 463, 467);
    }

    #[test]
    fn test_i64_public_div_public() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Public, 334, 0, 600, 606);
    }

    #[test]
    fn test_i64_public_div_private() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Private, 334, 0, 600, 606);
    }

    #[test]
    fn test_i64_private_div_public() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Public, 334, 0, 600, 606);
    }

    #[test]
    fn test_i64_private_div_private() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Private, 334, 0, 600, 606);
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
        run_test::<I>(Mode::Constant, Mode::Public, 4, 0, 261, 262);
    }

    #[test]
    fn test_u128_constant_div_private() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Private, 4, 0, 261, 262);
    }

    #[test]
    fn test_u128_public_div_constant() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Constant, 4, 0, 261, 262);
    }

    #[test]
    fn test_u128_private_div_constant() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Constant, 4, 0, 261, 262);
    }

    #[test]
    fn test_u128_public_div_public() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Public, 4, 0, 261, 262);
    }

    #[test]
    fn test_u128_public_div_private() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Private, 4, 0, 261, 262);
    }

    #[test]
    fn test_u128_private_div_public() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Public, 4, 0, 261, 262);
    }

    #[test]
    fn test_u128_private_div_private() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Private, 4, 0, 261, 262);
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
        run_overflow_and_halt_test::<I>(Mode::Constant, Mode::Public, 779, 0, 911, 915);
    }

    #[test]
    fn test_i128_constant_div_private() {
        type I = i128;
        run_overflow_and_halt_test::<I>(Mode::Constant, Mode::Private, 779, 0, 911, 915);
    }

    #[test]
    fn test_i128_public_div_constant() {
        type I = i128;
        run_overflow_and_halt_test::<I>(Mode::Public, Mode::Constant, 779, 0, 911, 915);
    }

    #[test]
    fn test_i128_private_div_constant() {
        type I = i128;
        run_overflow_and_halt_test::<I>(Mode::Private, Mode::Constant, 779, 0, 911, 915);
    }

    #[test]
    fn test_i128_public_div_public() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Public, 654, 0, 1176, 1182);
    }

    #[test]
    fn test_i128_public_div_private() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Private, 654, 0, 1176, 1182);
    }

    #[test]
    fn test_i128_private_div_public() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Public, 654, 0, 1176, 1182);
    }

    #[test]
    fn test_i128_private_div_private() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Private, 654, 0, 1176, 1182);
    }
}
