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

impl<E: Environment, I: IntegerType> Metrics<dyn DivChecked<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        match I::is_signed() {
            true => match (case.0, case.1) {
                (Mode::Constant, Mode::Constant) => Count::is(I::BITS, 0, 0, 0),
                (Mode::Constant, _) | (_, Mode::Constant) => {
                    Count::less_than(6 * I::BITS, 0, (7 * I::BITS) + 10, (8 * I::BITS) + 17)
                }
                (_, _) => Count::is(5 * I::BITS, 0, (8 * I::BITS) + 10, (8 * I::BITS) + 17),
            },
            false => match (case.0, case.1) {
                (Mode::Constant, Mode::Constant) => Count::is(I::BITS, 0, 0, 0),
                (Mode::Constant, _) | (_, Mode::Constant) => {
                    Count::less_than(0, 0, (2 * I::BITS) + 1, (2 * I::BITS) + 2)
                }
                (_, _) => Count::is(0, 0, (2 * I::BITS) + 1, (2 * I::BITS) + 2),
            },
        }
    }
}

impl<E: Environment, I: IntegerType> OutputMode<dyn DivChecked<Integer<E, I>, Output = Integer<E, I>>>
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
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};
    use test_utilities::*;

    use std::{ops::RangeInclusive, panic::RefUnwindSafe};

    const ITERATIONS: usize = 32;

    #[rustfmt::skip]
    fn check_div<I: IntegerType + std::panic::RefUnwindSafe>(
        name: &str,
        first: I,
        second: I,
        mode_a: Mode,
        mode_b: Mode
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);
        if second == I::zero() {
            check_operation_halts(&a, &b, Integer::div_checked);
        } else {
            match first.checked_div(&second) {
                Some(expected) => Circuit::scope(name, || {
                        let candidate = a.div_checked(&b);
                        assert_eq!(expected, candidate.eject_value());
                        assert_count!(Integer<Circuit, I>, DivChecked<Integer<Circuit, I>, Output = Integer<Circuit, I>>, &(mode_a, mode_b));
                        assert_output_mode!(candidate, Integer<Circuit, I>, DivChecked<Integer<Circuit, I>, Output = Integer<Circuit, I>>, &(mode_a, mode_b));
                    }),
                None => {
                    match (mode_a, mode_b) {
                        (Mode::Constant, Mode::Constant) => check_operation_halts(&a, &b, Integer::div_checked),
                        _ => Circuit::scope(name, || {
                            let _candidate = a.div_checked(&b);
                            assert_count_fails!(Integer<Circuit, I>, DivChecked<Integer<Circuit, I>, Output = Integer<Circuit, I>>, &(mode_a, mode_b));
                        })
                    }
                }
            }
        }
        Circuit::reset();
    }

    fn run_test<I: IntegerType + std::panic::RefUnwindSafe>(mode_a: Mode, mode_b: Mode) {
        for _ in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut test_rng());
            let second: I = UniformRand::rand(&mut test_rng());

            let name = format!("Div: {} / {}", first, second);
            check_div(&name, first, second, mode_a, mode_b);

            let name = format!("Div by One: {} / {}", first, I::one());
            check_div(&name, first, I::one(), mode_a, mode_b);

            let name = format!("Div by Self: {} / {}", first, first);
            check_div(&name, first, first, mode_a, mode_b);

            let name = format!("Div by Zero: {} / {}", first, I::zero());
            check_div(&name, first, I::zero(), mode_a, mode_b);
        }

        // Check standard division properties and corner cases.
        check_div("MAX / 1", I::MAX, I::one(), mode_a, mode_b);
        check_div("MIN / 1", I::MIN, I::one(), mode_a, mode_b);
        check_div("1 / 1", I::one(), I::one(), mode_a, mode_b);
        check_div("0 / 1", I::zero(), I::one(), mode_a, mode_b);
        check_div("MAX / 0", I::MAX, I::zero(), mode_a, mode_b);
        check_div("MIN / 0", I::MIN, I::zero(), mode_a, mode_b);
        check_div("1 / 0", I::one(), I::zero(), mode_a, mode_b);
        check_div("0 / 0", I::zero(), I::zero(), mode_a, mode_b);

        // Check some additional corner cases for signed integer division.
        if I::is_signed() {
            check_div("MAX / -1", I::MAX, I::zero() - I::one(), mode_a, mode_b);
            check_div("MIN / -1", I::MIN, I::zero() - I::one(), mode_a, mode_b);
            check_div("1 / -1", I::one(), I::zero() - I::one(), mode_a, mode_b);
        }
    }

    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe>(mode_a: Mode, mode_b: Mode)
    where
        RangeInclusive<I>: Iterator<Item = I>,
    {
        for first in I::MIN..=I::MAX {
            for second in I::MIN..=I::MAX {
                let name = format!("Div: ({} / {})", first, second);
                check_div(&name, first, second, mode_a, mode_b);
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
