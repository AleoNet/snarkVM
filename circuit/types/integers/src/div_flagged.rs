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

impl<E: Environment, I: IntegerType> DivFlagged<Self> for Integer<E, I> {
    type Output = (Self, Boolean<E>);

    #[inline]
    fn div_flagged(&self, other: &Integer<E, I>) -> Self::Output {
        match (self.is_constant(), other.is_constant()) {
            // If `other` is a constant and is zero, then return zero and set the flag.
            (_, true) if other.eject_value().is_zero() => (self.clone(), Boolean::constant(true)),
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

                    // Divide the absolute value of `self` and `other` in the base field.
                    // Note that it is safe to use `abs_wrapped`, since the case for console::Integer::MIN is handled above.
                    let unsigned_dividend = self.abs_wrapped().cast_as_dual();
                    // Note that `unsigned_divisor` is zero iff `other` is zero.
                    let unsigned_divisor = other.abs_wrapped().cast_as_dual();
                    let unsigned_quotient =
                        unsigned_dividend.flagged_wrapped_division(&unsigned_divisor, &divisor_is_zero);

                    // Note that quotient <= |console::Integer::MIN|, since the dividend <= |console::Integer::MIN| and 0 <= quotient <= dividend.
                    let signed_quotient = Integer { bits_le: unsigned_quotient.bits_le, phantom: Default::default() };
                    let operands_same_sign = &self.msb().is_equal(other.msb());

                    (
                        Self::ternary(
                            operands_same_sign,
                            &signed_quotient,
                            &Self::zero().sub_wrapped(&signed_quotient),
                        ),
                        overflows | divisor_is_zero,
                    )
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
                self.flagged_unsigned_division_via_witness(other, divisor_is_zero).0
            } else {
                Self::ternary(divisor_is_zero, self, &self.unsigned_binary_long_division(other).0)
            }
        }
    }

    /// Divides `self` by `other`, via witnesses, returning the quotient and remainder.
    /// This method does not check that `other` is non-zero.
    /// This method should only be used when 2 * I::BITS < E::BaseField::size_in_data_bits().
    pub(super) fn flagged_unsigned_division_via_witness(
        &self,
        other: &Self,
        divisor_is_zero: &Boolean<E>,
    ) -> (Self, Self) {
        // Eject the dividend and divisor, to compute the quotient as a witness.
        let dividend_value = self.eject_value();
        // Note: This band-aid was added to prevent a panic when the divisor is 0.
        let divisor_value = match other.eject_value().is_zero() {
            true => console::Integer::one(),
            false => other.eject_value(),
        };

        // Overflow is not possible for unsigned integers so we use wrapping operations.
        let quotient = Integer::new(Mode::Private, console::Integer::new(dividend_value.wrapping_div(&divisor_value)));
        let remainder = Integer::new(Mode::Private, console::Integer::new(dividend_value.wrapping_rem(&divisor_value)));

        let self_equals_quotient_times_other_plus_remainder =
            self.to_field().is_equal(&(quotient.to_field() * other.to_field() + remainder.to_field()));

        // If the divisor is not zero, ensure that Euclidean division holds for these values in the base field.
        // This is equivalent to `!divisor_is_zero ==> (self == quotient * other + remainder)`.
        // Which is equivalent to `divisor_is_zero || (self == quotient * other + remainder)`.

        println!("divisor_is_zero: {:?}", divisor_is_zero);

        E::assert(divisor_is_zero.bitor(&self_equals_quotient_times_other_plus_remainder));
        println!(
            "divisor_is_zero ==> (self == quotient * other + remainder): {:?}",
            divisor_is_zero.bitor(&self_equals_quotient_times_other_plus_remainder)
        );

        // If the divisor is not zero, ensure that the remainder is less than the divisor.
        // This is equivalent to `!divisor_is_zero ==> (remainder < other)`.
        // Which is equivalent to `divisor_is_zero || (remainder < other)`.
        E::assert(divisor_is_zero.bitor(&remainder.is_less_than(other)));
        println!(
            "divisor_is_zero ==> (remainder < other): {:?}",
            divisor_is_zero.bitor(&remainder.is_less_than(other))
        );

        // Return the quotient of `self` and `other`.
        (quotient, remainder)
    }
}

impl<E: Environment, I: IntegerType> Metrics<dyn DivFlagged<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        match I::is_signed() {
            true => match (case.0, case.1) {
                (Mode::Constant, Mode::Constant) => Count::is(2 * I::BITS, 0, 0, 0),
                (Mode::Constant, _) | (_, Mode::Constant) => {
                    Count::less_than(9 * I::BITS, 0, (8 * I::BITS) + 2, (8 * I::BITS) + 12)
                }
                (_, _) => Count::is(8 * I::BITS, 0, (10 * I::BITS) + 15, (10 * I::BITS) + 27),
            },
            false => match (case.0, case.1) {
                (Mode::Constant, Mode::Constant) => Count::is(2 * I::BITS, 0, 0, 0),
                (_, Mode::Constant) => Count::is(2 * I::BITS, 0, (3 * I::BITS) + 1, (3 * I::BITS) + 4),
                (Mode::Constant, _) | (_, _) => Count::is(2 * I::BITS, 0, (3 * I::BITS) + 4, (3 * I::BITS) + 9),
            },
        }
    }
}

impl<E: Environment, I: IntegerType> OutputMode<dyn DivFlagged<Integer<E, I>, Output = Integer<E, I>>>
    for Integer<E, I>
{
    type Case = (Mode, Mode);

    fn output_mode(case: &Self::Case) -> Mode {
        match (case.0, case.1) {
            (Mode::Constant, Mode::Constant) => Mode::Constant,
            (_, _) => Mode::Private,
        }
    }
}

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
        let (expected_result, expected_flag) = first.overflowing_div(&second);
        println!("{}: {} / {} = {}, {}", name, first, second, expected_result, expected_flag);
        Circuit::scope(name, || {
            let (candidate_result, candidate_flag) = a.div_flagged(&b);
            assert_eq!(expected_result, *candidate_result.eject_value());
            assert_eq!(expected_flag, candidate_flag.eject_value());
            assert_eq!(console::Integer::new(expected_result), candidate_result.eject_value());
            // assert_count!(DivWrapped(Integer<I>, Integer<I>) => Integer<I>, &(mode_a, mode_b));
            // assert_output_mode!(DivWrapped(Integer<I>, Integer<I>) => Integer<I>, &(mode_a, mode_b), candidate);
            assert!(Circuit::is_satisfied_in_scope(), "(is_satisfied_in_scope)");
        });
        Circuit::reset();
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
