// Copyright (C) 2019-2023 Aleo Systems Inc.
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

impl<E: Environment, I: IntegerType> DivFlagged<Self> for Integer<E, I> {
    type Output = (Self, Boolean<E>);

    #[inline]
    fn div_flagged(&self, other: &Integer<E, I>) -> Self::Output {
        match (self.is_constant(), other.is_constant()) {
            // If `other` is a constant and is zero, then return zero and set the flag.
            (_, true) if other.eject_value().is_zero() => (Self::zero(), Boolean::constant(true)),
            // If `self` and `other` are constants, and other is not zero, then directly return the value of the division and the flag.
            (true, true) => {
                witness!(|self, other| {
                    let (result, flag) = self.overflowing_div(&other);
                    (console::Integer::new(result), flag)
                })
            }
            // Handle the remaining cases.
            // Note that `other` is either a constant and non-zero, or not a constant.
            _ => {
                if I::is_signed() {
                    // Ensure that overflow cannot occur in this division.
                    // Signed integer division wraps when the dividend is Integer::MIN and the divisor is -1.
                    let min = Integer::constant(console::Integer::MIN);
                    let neg_one = Integer::constant(-console::Integer::one());
                    let overflows = self.is_equal(&min) & other.is_equal(&neg_one);
                    let divisor_is_zero = other.is_equal(&Self::zero());

                    (self.flagged_wrapped_division(other, &divisor_is_zero), overflows | divisor_is_zero)
                } else {
                    let divisor_is_zero = other.is_equal(&Self::zero());
                    // Return the quotient of `self` and `other`.
                    (self.flagged_wrapped_division(other, &divisor_is_zero), divisor_is_zero)
                }
            }
        }
    }
}

impl<E: Environment, I: IntegerType> Integer<E, I> {
    /// Returns the quotient of `self` and `other`.
    /// This method does not check that `other` is not zero.
    /// This method uses the flag `divisor_is_zero` to conditionally check that the results of the division are well formed, as long as the divisor is not zero.
    fn flagged_wrapped_division(&self, other: &Self, divisor_is_zero: &Boolean<E>) -> Self {
        if I::is_signed() {
            // Divide the absolute value of `self` and `other` in the base field.
            let unsigned_dividend = self.abs_wrapped().cast_as_dual();
            // Note that `unsigned_divisor` is zero iff `other` is zero.
            let unsigned_divisor = other.abs_wrapped().cast_as_dual();
            let unsigned_quotient = unsigned_dividend.flagged_wrapped_division(&unsigned_divisor, divisor_is_zero);

            //  Note that quotient <= |console::Integer::MIN|, since the dividend <= |console::Integer::MIN| and 0 <= quotient <= dividend.
            let signed_quotient = Self { bits_le: unsigned_quotient.bits_le, phantom: Default::default() };
            let operands_same_sign = &self.msb().is_equal(other.msb());

            // Note that this expression handles the wrapping case, where the dividend is `I::MIN` and the divisor is `-1` and the result should be `I::MIN`.
            Self::ternary(operands_same_sign, &signed_quotient, &Self::zero().sub_wrapped(&signed_quotient))
        } else {
            // If the product of two unsigned integers can fit in the base field, then we can perform an optimized division operation.
            if 2 * I::BITS < E::BaseField::size_in_data_bits() as u64 {
                let enforce_flagged_division = |first: &Self, second: &Self, quotient: &Self, remainder: &Self| {
                    let first_equals_quotient_times_other_plus_remainder =
                        first.to_field().is_equal(&(quotient.to_field() * second.to_field() + remainder.to_field()));

                    // If the divisor is not zero, ensure that Euclidean division holds for these values in the base field.
                    // This is equivalent to `!divisor_is_zero ==> (self == quotient * other + remainder)`.
                    // Which is equivalent to `divisor_is_zero || (self == quotient * other + remainder)`.
                    E::assert((divisor_is_zero).bitor(&first_equals_quotient_times_other_plus_remainder));

                    // If the divisor is not zero, ensure that the remainder is less than the divisor.
                    // This is equivalent to `!divisor_is_zero ==> (remainder < other)`.
                    // Which is equivalent to `divisor_is_zero || (remainder < other)`.
                    E::assert((divisor_is_zero).bitor(&remainder.is_less_than(other)));
                };
                self.unsigned_division_via_witness(other, enforce_flagged_division).0
            } else {
                Self::ternary(divisor_is_zero, &Self::zero(), &self.unsigned_binary_long_division(other).0)
            }
        }
    }
}

// TODO: `Count` and `OutputMode`.

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    use test_utilities::*;

    use std::{ops::RangeInclusive, panic::RefUnwindSafe};

    const ITERATIONS: u64 = 32;

    fn check_div<I: IntegerType + RefUnwindSafe>(
        name: &str,
        first: console::Integer<<Circuit as Environment>::Network, I>,
        second: console::Integer<<Circuit as Environment>::Network, I>,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);

        // Check that the flagged implementation produces the correct result.
        let (expected_result, expected_flag) = first.overflowing_div(&second);
        Circuit::scope(name, || {
            let (candidate_result, candidate_flag) = a.div_flagged(&b);
            assert_eq!(expected_result, *candidate_result.eject_value());
            assert_eq!(expected_flag, candidate_flag.eject_value());
            assert_eq!(console::Integer::new(expected_result), candidate_result.eject_value());
            assert!(Circuit::is_satisfied_in_scope(), "(is_satisfied_in_scope)");
        });
        Circuit::reset();

        let (flagged_result, flag) = a.div_flagged(&b);

        // Check that the flagged implementation matches the checked implementation.
        match (flag.eject_value(), second.is_zero()) {
            (_, true) => match mode_b {
                // If the divisor is zero, and the mode is constant, then checked implementation should halt.
                Mode::Constant => check_operation_halts(&a, &b, Integer::div_checked),
                // Otherwise, the circuit should be unsatisfied.
                _ => {
                    // On division by zero, the flagged result should be zero and the flag should be set.
                    assert_eq!(flagged_result.eject_value(), console::Integer::zero());
                    assert!(flag.eject_value());
                    // On division by zero, the checked implementation should not be satisfied.
                    Circuit::scope(name, || {
                        let _ = a.div_checked(&b);
                        assert!(!Circuit::is_satisfied_in_scope());
                    });
                    Circuit::reset();
                }
            },
            // If the flag is set and the mode is constant, the checked implementation should halt.
            (true, _) if mode_a == Mode::Constant && mode_b == Mode::Constant => {
                check_operation_halts(&a, &b, Integer::div_checked)
            }
            // Otherwise, the flagged implementation should match the checked implementation.
            _ => {
                Circuit::scope(name, || {
                    let checked_result = a.div_checked(&b);
                    assert_eq!(flagged_result.eject_value(), checked_result.eject_value());
                    match flag.eject_value() {
                        // If the flag is set, the circuit should not be satisfied.
                        true => assert!(!Circuit::is_satisfied_in_scope()),
                        // If the flag is not set, the circuit should be satisfied.
                        false => assert!(Circuit::is_satisfied_in_scope()),
                    }
                });
                Circuit::reset();
            }
        }
    }

    fn run_test<I: IntegerType + RefUnwindSafe>(mode_a: Mode, mode_b: Mode) {
        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            let first = Uniform::rand(&mut rng);
            let second = Uniform::rand(&mut rng);

            let name = format!("Div: {} / {}", first, second);
            check_div::<I>(&name, first, second, mode_a, mode_b);

            let name = format!("Div by One: {} / 1", first);
            check_div::<I>(&name, first, console::Integer::one(), mode_a, mode_b);

            let name = format!("Div by Self: {} / {}", first, first);
            check_div::<I>(&name, first, first, mode_a, mode_b);

            let name = format!("Div by Zero: {} / 0", first);
            check_div::<I>(&name, first, console::Integer::zero(), mode_a, mode_b);
        }

        // Check standard division properties and corner cases.
        check_div::<I>("MAX / 1", console::Integer::MAX, console::Integer::one(), mode_a, mode_b);
        check_div::<I>("MIN / 1", console::Integer::MIN, console::Integer::one(), mode_a, mode_b);
        check_div::<I>("1 / 1", console::Integer::one(), console::Integer::one(), mode_a, mode_b);
        check_div::<I>("0 / 1", console::Integer::zero(), console::Integer::one(), mode_a, mode_b);
        check_div::<I>("MAX / 0", console::Integer::MAX, console::Integer::zero(), mode_a, mode_b);
        check_div::<I>("MIN / 0", console::Integer::MIN, console::Integer::zero(), mode_a, mode_b);
        check_div::<I>("1 / 0", console::Integer::one(), console::Integer::zero(), mode_a, mode_b);
        check_div::<I>("0 / 0", console::Integer::zero(), console::Integer::zero(), mode_a, mode_b);

        // Check some additional corner cases for signed integer division.
        if I::is_signed() {
            check_div::<I>("MAX / -1", console::Integer::MAX, -console::Integer::one(), mode_a, mode_b);
            check_div::<I>("MIN / -1", console::Integer::MIN, -console::Integer::one(), mode_a, mode_b);
            check_div::<I>("1 / -1", console::Integer::one(), -console::Integer::one(), mode_a, mode_b);
        }
    }

    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe>(mode_a: Mode, mode_b: Mode)
    where
        RangeInclusive<I>: Iterator<Item = I>,
    {
        for first in I::MIN..=I::MAX {
            for second in I::MIN..=I::MAX {
                let first = console::Integer::<_, I>::new(first);
                let second = console::Integer::<_, I>::new(second);

                let name = format!("Div: ({} / {})", first, second);
                check_div::<I>(&name, first, second, mode_a, mode_b);
            }
        }
    }

    test_integer_binary!(run_test, i8, div);
    test_integer_binary!(run_test, i16, div);
    test_integer_binary!(run_test, i32, div);
    test_integer_binary!(run_test, i64, div);
    test_integer_binary!(run_test, i128, div);

    test_integer_binary!(run_test, u8, div);
    test_integer_binary!(run_test, u16, div);
    test_integer_binary!(run_test, u32, div);
    test_integer_binary!(run_test, u64, div);
    test_integer_binary!(run_test, u128, div);

    test_integer_binary!(#[ignore], run_exhaustive_test, u8, div, exhaustive);
    test_integer_binary!(#[ignore], run_exhaustive_test, i8, div, exhaustive);
}
