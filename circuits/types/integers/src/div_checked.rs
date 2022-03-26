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

impl<E: Environment, I: IntegerType> Div<Integer<E, I>> for Integer<E, I> {
    type Output = Self;

    fn div(self, other: Self) -> Self::Output {
        self / &other
    }
}

impl<E: Environment, I: IntegerType> Div<Integer<E, I>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn div(self, other: Integer<E, I>) -> Self::Output {
        self / &other
    }
}

impl<E: Environment, I: IntegerType> Div<&Integer<E, I>> for Integer<E, I> {
    type Output = Self;

    fn div(self, other: &Self) -> Self::Output {
        &self / other
    }
}

impl<E: Environment, I: IntegerType> Div<&Integer<E, I>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn div(self, other: &Integer<E, I>) -> Self::Output {
        let mut output = self.clone();
        output /= other;
        output
    }
}

impl<E: Environment, I: IntegerType> DivAssign<Integer<E, I>> for Integer<E, I> {
    fn div_assign(&mut self, other: Integer<E, I>) {
        *self /= &other;
    }
}

impl<E: Environment, I: IntegerType> DivAssign<&Integer<E, I>> for Integer<E, I> {
    fn div_assign(&mut self, other: &Integer<E, I>) {
        // Stores the quotient of `self` and `other` in `self`.
        *self = self.div_checked(other);
    }
}

impl<E: Environment, I: IntegerType> DivChecked<Self> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn div_checked(&self, other: &Integer<E, I>) -> Self::Output {
        // Halt on division by zero as there is no sound way to perform this operation.
        if other.eject_value().is_zero() {
            E::halt("Division by zero error")
        }

        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the quotient and return the new constant.
            match self.eject_value().checked_div(&other.eject_value()) {
                Some(value) => Integer::constant(value),
                None => E::halt("Overflow or underflow on division of two integer constants"),
            }
        } else if I::is_signed() {
            // Ensure that overflow cannot occur in this division.
            // Signed integer division wraps when the dividend is I::MIN and the divisor is -1.
            let min = Integer::constant(I::MIN);
            let neg_one = Integer::constant(I::zero() - I::one());
            let overflows = self.is_equal(&min) & other.is_equal(&neg_one);
            E::assert_eq(overflows, E::zero());

            // Divide the absolute value of `self` and `other` in the base field.
            // Note that it is safe to use `abs_wrapped`, since the case for I::MIN is handled above.
            let unsigned_dividend = self.abs_wrapped().cast_as_dual();
            let unsigned_divisor = other.abs_wrapped().cast_as_dual();
            let unsigned_quotient = unsigned_dividend.div_wrapped(&unsigned_divisor);

            // TODO (@pranav) Do we need to check that the quotient cannot exceed abs(I::MIN)?
            //  This is implicitly true since the dividend <= abs(I::MIN) and 0 <= quotient <= dividend.
            let signed_quotient = Integer { bits_le: unsigned_quotient.bits_le, phantom: Default::default() };
            let operands_same_sign = &self.msb().is_equal(other.msb());

            Self::ternary(operands_same_sign, &signed_quotient, &Self::zero().sub_wrapped(&signed_quotient))
        } else {
            // Return the quotient of `self` and `other`.
            self.div_wrapped(other)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};
    use test_utilities::*;

    use std::{ops::RangeInclusive, panic::RefUnwindSafe};

    const ITERATIONS: usize = 32;

    #[rustfmt::skip]
    fn check_div_without_expected_numbers<I: IntegerType + std::panic::RefUnwindSafe>(
        name: &str,
        first: I,
        second: I,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);
        let case = format!("({} / {})", a.eject_value(), b.eject_value());
        if second == I::zero() {
            check_operation_halts(&a, &b, Integer::div_checked);
        } else {
            match first.checked_div(&second) {
                Some(value) => check_operation_passes_without_counts(name, &case, value, &a, &b, Integer::div_checked),
                None => {
                    match (mode_a, mode_b) {
                        (Mode::Constant, Mode::Constant) => check_operation_halts(&a, &b, Integer::div_checked),
                        _ => check_operation_fails_without_counts(name, &case, &a, &b, Integer::div_checked)
                    }
                }
            }
        }
    }

    #[rustfmt::skip]
    fn check_div<I: IntegerType + std::panic::RefUnwindSafe>(
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
        let case = format!("({} / {})", a.eject_value(), b.eject_value());
        if second == I::zero() {
            check_operation_halts(&a, &b, Integer::div_checked);
        } else {
            match first.checked_div(&second) {
                Some(value) => check_operation_passes(name, &case, value, &a, &b, Integer::div_checked, num_constants, num_public, num_private, num_constraints),
                None => {
                    match (mode_a, mode_b) {
                        (Mode::Constant, Mode::Constant) => check_operation_halts(&a, &b, Integer::div_checked),
                        _ => check_operation_fails(name, &case, &a, &b, Integer::div_checked, num_constants, num_public, num_private, num_constraints)
                    }
                }
            }
        }
    }

    #[rustfmt::skip]
    fn run_overflow_and_corner_case_test<I: IntegerType + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let check_div = | name: &str, first: I, second: I | check_div_without_expected_numbers(name, first, second, mode_a, mode_b);

        for _ in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut test_rng());
            let second: I = UniformRand::rand(&mut test_rng());

            let name = format!("Div: {} / {}", first, second);
            check_div(&name, first, second);

            let name = format!("Div by One: {} / {}", first, I::one());
            check_div(&name, first, I::one());

            let name = format!("Div by Self: {} / {}", first, first);
            check_div(&name, first, first);

            let name = format!("Div by Zero: {} / {}", first, I::zero());
            check_div(&name, first, I::zero());
        }

        // Check standard division properties and corner cases.
        check_div("MAX / 1", I::MAX, I::one());
        check_div("MIN / 1", I::MIN, I::one());
        check_div("1 / 1", I::one(), I::one());
        check_div("0 / 1", I::zero(), I::one());
        check_div("MAX / 0", I::MAX, I::zero());
        check_div("MIN / 0", I::MIN, I::zero());
        check_div("1 / 0", I::one(), I::zero());
        check_div("0 / 0", I::zero(),I::zero());

        // Check some additional corner cases for signed integer division.
        if I::is_signed() {
            check_div("MAX / -1", I::MAX, I::zero() - I::one());
            check_div("MIN / -1", I::MIN, I::zero() - I::one());
            check_div("1 / -1", I::one(), I::zero() - I::one());
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
        let check_div = | name: &str, first: I, second: I | check_div(name, first, second, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);

        for _ in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut test_rng());
            let second: I = UniformRand::rand(&mut test_rng());

            let name = format!("Div: {} / {}", first, second);
            check_div(&name, first, second);

            let name = format!("Div by One: {} / {}", first, I::one());
            check_div(&name, first, I::one());

            let name = format!("Div by Self: {} / {}", first, first);
            check_div(&name, first, first);

            let name = format!("Div by Zero: {} / {}", first, I::zero());
            check_div(&name, first, I::zero());
        }

        // Check standard division properties and corner cases.
        check_div("MAX / 1", I::MAX, I::one());
        check_div("MIN / 1", I::MIN, I::one());
        check_div("1 / 1", I::one(), I::one());
        check_div("0 / 1", I::zero(), I::one());
        check_div("MAX / 0", I::MAX, I::zero());
        check_div("MIN / 0", I::MIN, I::zero());
        check_div("1 / 0", I::one(), I::zero());
        check_div("0 / 0", I::zero(),I::zero());

        // Check some additional corner cases for signed integer division.
        if I::is_signed() {
            check_div("MAX / -1", I::MAX, I::zero() - I::one());
            check_div("MIN / -1", I::MIN, I::zero() - I::one());
            check_div("1 / -1", I::one(), I::zero() - I::one());
        }
    }

    #[rustfmt::skip]
    fn run_exhaustive_test_without_expected_numbers<I: IntegerType + RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode
    ) where
        RangeInclusive<I>: Iterator<Item = I>
    {
        for first in I::MIN..=I::MAX {
            for second in I::MIN..=I::MAX {
                let name = format!("Div: ({} / {})", first, second);
                check_div_without_expected_numbers(&name, first, second, mode_a, mode_b);
            }
        }
    }

    #[rustfmt::skip]
    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) where
        RangeInclusive<I>: Iterator<Item = I>
    {
        for first in I::MIN..=I::MAX {
            for second in I::MIN..=I::MAX {
                let name = format!("Div: ({} / {})", first, second);
                check_div(&name, first, second, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
            }
        }
    }

    #[test]
    fn test_u8_constant_div_constant() {
        type I = u8;
        run_overflow_and_corner_case_test::<I>(Mode::Constant, Mode::Constant);
        run_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_div_public() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 17, 18);
    }

    #[test]
    fn test_u8_constant_div_private() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 17, 18);
    }

    #[test]
    fn test_u8_public_div_constant() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 16, 17);
    }

    #[test]
    fn test_u8_private_div_constant() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 16, 17);
    }

    #[test]
    fn test_u8_public_div_public() {
        type I = u8;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Public);
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 17, 18);
    }

    #[test]
    fn test_u8_public_div_private() {
        type I = u8;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Private);
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 17, 18);
    }

    #[test]
    fn test_u8_private_div_public() {
        type I = u8;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Public);
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 17, 18);
    }

    #[test]
    fn test_u8_private_div_private() {
        type I = u8;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Private);
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 17, 18);
    }

    // Tests for i8

    #[test]
    fn test_i8_constant_div_constant() {
        type I = i8;
        run_overflow_and_corner_case_test::<I>(Mode::Constant, Mode::Constant);
        run_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_div_public() {
        type I = i8;
        run_overflow_and_corner_case_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i8_constant_div_private() {
        type I = i8;
        run_overflow_and_corner_case_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i8_public_div_constant() {
        type I = i8;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i8_private_div_constant() {
        type I = i8;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i8_public_div_public() {
        type I = i8;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Public);
        run_test::<I>(Mode::Public, Mode::Public, 40, 0, 74, 81);
    }

    #[test]
    fn test_i8_public_div_private() {
        type I = i8;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Private);
        run_test::<I>(Mode::Public, Mode::Private, 40, 0, 74, 81);
    }

    #[test]
    fn test_i8_private_div_public() {
        type I = i8;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Public);
        run_test::<I>(Mode::Private, Mode::Public, 40, 0, 74, 81);
    }

    #[test]
    fn test_i8_private_div_private() {
        type I = i8;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Private);
        run_test::<I>(Mode::Private, Mode::Private, 40, 0, 74, 81);
    }

    // Tests for u16

    #[test]
    fn test_u16_constant_div_constant() {
        type I = u16;
        run_overflow_and_corner_case_test::<I>(Mode::Constant, Mode::Constant);
        run_test::<I>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_div_public() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 33, 34);
    }

    #[test]
    fn test_u16_constant_div_private() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 33, 34);
    }

    #[test]
    fn test_u16_public_div_constant() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 32, 33);
    }

    #[test]
    fn test_u16_private_div_constant() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 32, 33);
    }

    #[test]
    fn test_u16_public_div_public() {
        type I = u16;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Public);
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 33, 34);
    }

    #[test]
    fn test_u16_public_div_private() {
        type I = u16;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Private);
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 33, 34);
    }

    #[test]
    fn test_u16_private_div_public() {
        type I = u16;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Public);
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 33, 34);
    }

    #[test]
    fn test_u16_private_div_private() {
        type I = u16;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Private);
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 33, 34);
    }

    // Tests for i16

    #[test]
    fn test_i16_constant_div_constant() {
        type I = i16;
        run_overflow_and_corner_case_test::<I>(Mode::Constant, Mode::Constant);
        run_test::<I>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_div_public() {
        type I = i16;
        run_overflow_and_corner_case_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i16_constant_div_private() {
        type I = i16;
        run_overflow_and_corner_case_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i16_public_div_constant() {
        type I = i16;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i16_private_div_constant() {
        type I = i16;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i16_public_div_public() {
        type I = i16;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Public);
        run_test::<I>(Mode::Public, Mode::Public, 80, 0, 138, 145);
    }

    #[test]
    fn test_i16_public_div_private() {
        type I = i16;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Private);
        run_test::<I>(Mode::Public, Mode::Private, 80, 0, 138, 145);
    }

    #[test]
    fn test_i16_private_div_public() {
        type I = i16;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Public);
        run_test::<I>(Mode::Private, Mode::Public, 80, 0, 138, 145);
    }

    #[test]
    fn test_i16_private_div_private() {
        type I = i16;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Private);
        run_test::<I>(Mode::Private, Mode::Private, 80, 0, 138, 145);
    }

    // Tests for u32

    #[test]
    fn test_u32_constant_div_constant() {
        type I = u32;
        run_overflow_and_corner_case_test::<I>(Mode::Constant, Mode::Constant);
        run_test::<I>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_div_public() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 65, 66);
    }

    #[test]
    fn test_u32_constant_div_private() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 65, 66);
    }

    #[test]
    fn test_u32_public_div_constant() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 64, 65);
    }

    #[test]
    fn test_u32_private_div_constant() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 64, 65);
    }

    #[test]
    fn test_u32_public_div_public() {
        type I = u32;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Public);
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 65, 66);
    }

    #[test]
    fn test_u32_public_div_private() {
        type I = u32;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Private);
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 65, 66);
    }

    #[test]
    fn test_u32_private_div_public() {
        type I = u32;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Public);
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 65, 66);
    }

    #[test]
    fn test_u32_private_div_private() {
        type I = u32;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Private);
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 65, 66);
    }

    // Tests for i32

    #[test]
    fn test_i32_constant_div_constant() {
        type I = i32;
        run_overflow_and_corner_case_test::<I>(Mode::Constant, Mode::Constant);
        run_test::<I>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_div_public() {
        type I = i32;
        run_overflow_and_corner_case_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i32_constant_div_private() {
        type I = i32;
        run_overflow_and_corner_case_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i32_public_div_constant() {
        type I = i32;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i32_private_div_constant() {
        type I = i32;
        run_overflow_and_corner_case_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i32_public_div_public() {
        type I = i32;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Public);
        run_test::<I>(Mode::Public, Mode::Public, 160, 0, 266, 273);
    }

    #[test]
    fn test_i32_public_div_private() {
        type I = i32;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Private);
        run_test::<I>(Mode::Public, Mode::Private, 160, 0, 266, 273);
    }

    #[test]
    fn test_i32_private_div_public() {
        type I = i32;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Public);
        run_test::<I>(Mode::Private, Mode::Public, 160, 0, 266, 273);
    }

    #[test]
    fn test_i32_private_div_private() {
        type I = i32;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Private);
        run_test::<I>(Mode::Private, Mode::Private, 160, 0, 266, 273);
    }

    // Tests for u64

    #[test]
    fn test_u64_constant_div_constant() {
        type I = u64;
        run_overflow_and_corner_case_test::<I>(Mode::Constant, Mode::Constant);
        run_test::<I>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_div_public() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 129, 130);
    }

    #[test]
    fn test_u64_constant_div_private() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 129, 130);
    }

    #[test]
    fn test_u64_public_div_constant() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 128, 129);
    }

    #[test]
    fn test_u64_private_div_constant() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 128, 129);
    }

    #[test]
    fn test_u64_public_div_public() {
        type I = u64;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Public);
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 129, 130);
    }

    #[test]
    fn test_u64_public_div_private() {
        type I = u64;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Private);
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 129, 130);
    }

    #[test]
    fn test_u64_private_div_public() {
        type I = u64;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Public);
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 129, 130);
    }

    #[test]
    fn test_u64_private_div_private() {
        type I = u64;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Private);
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 129, 130);
    }

    // Tests for i64

    #[test]
    fn test_i64_constant_div_constant() {
        type I = i64;
        run_overflow_and_corner_case_test::<I>(Mode::Constant, Mode::Constant);
        run_test::<I>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_div_public() {
        type I = i64;
        run_overflow_and_corner_case_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i64_constant_div_private() {
        type I = i64;
        run_overflow_and_corner_case_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i64_public_div_constant() {
        type I = i64;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i64_private_div_constant() {
        type I = i64;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i64_public_div_public() {
        type I = i64;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Public);
        run_test::<I>(Mode::Public, Mode::Public, 320, 0, 522, 529);
    }

    #[test]
    fn test_i64_public_div_private() {
        type I = i64;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Private);
        run_test::<I>(Mode::Public, Mode::Private, 320, 0, 522, 529);
    }

    #[test]
    fn test_i64_private_div_public() {
        type I = i64;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Public);
        run_test::<I>(Mode::Private, Mode::Public, 320, 0, 522, 529);
    }

    #[test]
    fn test_i64_private_div_private() {
        type I = i64;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Private);
        run_test::<I>(Mode::Private, Mode::Private, 320, 0, 522, 529);
    }

    // Tests for u128

    #[test]
    fn test_u128_constant_div_constant() {
        type I = u128;
        run_overflow_and_corner_case_test::<I>(Mode::Constant, Mode::Constant);
        run_test::<I>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_div_public() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Public, 0, 0, 257, 258);
    }

    #[test]
    fn test_u128_constant_div_private() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Private, 0, 0, 257, 258);
    }

    #[test]
    fn test_u128_public_div_constant() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Constant, 0, 0, 256, 257);
    }

    #[test]
    fn test_u128_private_div_constant() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Constant, 0, 0, 256, 257);
    }

    #[test]
    fn test_u128_public_div_public() {
        type I = u128;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Public);
        run_test::<I>(Mode::Public, Mode::Public, 0, 0, 257, 258);
    }

    #[test]
    fn test_u128_public_div_private() {
        type I = u128;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Private);
        run_test::<I>(Mode::Public, Mode::Private, 0, 0, 257, 258);
    }

    #[test]
    fn test_u128_private_div_public() {
        type I = u128;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Public);
        run_test::<I>(Mode::Private, Mode::Public, 0, 0, 257, 258);
    }

    #[test]
    fn test_u128_private_div_private() {
        type I = u128;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Private);
        run_test::<I>(Mode::Private, Mode::Private, 0, 0, 257, 258);
    }

    // Tests for i128

    #[test]
    fn test_i128_constant_div_constant() {
        type I = i128;
        run_overflow_and_corner_case_test::<I>(Mode::Constant, Mode::Constant);
        run_test::<I>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_div_public() {
        type I = i128;
        run_overflow_and_corner_case_test::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i128_constant_div_private() {
        type I = i128;
        run_overflow_and_corner_case_test::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i128_public_div_constant() {
        type I = i128;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i128_private_div_constant() {
        type I = i128;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i128_public_div_public() {
        type I = i128;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Public);
        run_test::<I>(Mode::Public, Mode::Public, 640, 0, 1034, 1041);
    }

    #[test]
    fn test_i128_public_div_private() {
        type I = i128;
        run_overflow_and_corner_case_test::<I>(Mode::Public, Mode::Private);
        run_test::<I>(Mode::Public, Mode::Private, 640, 0, 1034, 1041);
    }

    #[test]
    fn test_i128_private_div_public() {
        type I = i128;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Public);
        run_test::<I>(Mode::Private, Mode::Public, 640, 0, 1034, 1041);
    }

    #[test]
    fn test_i128_private_div_private() {
        type I = i128;
        run_overflow_and_corner_case_test::<I>(Mode::Private, Mode::Private);
        run_test::<I>(Mode::Private, Mode::Private, 640, 0, 1034, 1041);
    }

    // Exhaustive tests for u8.

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_div_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_div_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Private, 0, 0, 17, 18);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_div_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Private, 0, 0, 17, 18);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_div_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Constant, 0, 0, 16, 17);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_div_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Constant, 0, 0, 16, 17);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_div_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Public, 0, 0, 17, 18);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_div_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Private, 0, 0, 17, 18);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_div_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Public, 0, 0, 17, 18);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_div_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Private, 0, 0, 17, 18);
    }

    // Tests for i8

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_div_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_div_public() {
        type I = i8;
        run_exhaustive_test_without_expected_numbers::<I>(Mode::Constant, Mode::Public);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_div_private() {
        type I = i8;
        run_exhaustive_test_without_expected_numbers::<I>(Mode::Constant, Mode::Private);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_div_constant() {
        type I = i8;
        run_exhaustive_test_without_expected_numbers::<I>(Mode::Public, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_div_constant() {
        type I = i8;
        run_exhaustive_test_without_expected_numbers::<I>(Mode::Private, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_div_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Public, 40, 0, 74, 81);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_div_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Private, 40, 0, 74, 81);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_div_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Public, 40, 0, 74, 81);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_div_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Private, 40, 0, 74, 81);
    }
}
