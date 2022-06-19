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

impl<E: Environment, I: IntegerType> DivWrapped<Self> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn div_wrapped(&self, other: &Integer<E, I>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Halt on division by zero.
            E::assert(other.is_not_equal(&Self::zero()));
            // Compute the quotient and return the new constant.
            Integer::new(Mode::Constant, console::Integer::new(self.eject_value().wrapping_div(&other.eject_value())))
        } else if I::is_signed() {
            // Ensure this is not a division by zero.
            E::assert(other.is_not_equal(&Self::zero()));

            // Divide the absolute value of `self` and `other` in the base field.
            let unsigned_dividend = self.abs_wrapped().cast_as_dual();
            let unsigned_divisor = other.abs_wrapped().cast_as_dual();
            let unsigned_quotient = unsigned_dividend.div_wrapped(&unsigned_divisor);

            // TODO (@pranav) Do we need to check that the quotient cannot exceed abs(console::Integer::MIN)?
            //  This is implicitly true since the dividend <= abs(console::Integer::MIN) and 0 <= quotient <= dividend.
            let signed_quotient = Self { bits_le: unsigned_quotient.bits_le, phantom: Default::default() };
            let operands_same_sign = &self.msb().is_equal(other.msb());
            let signed_quotient =
                Self::ternary(operands_same_sign, &signed_quotient, &Self::zero().sub_wrapped(&signed_quotient));

            // Signed integer division wraps when the dividend is Integer::MIN and the divisor is -1.
            let min = Self::constant(console::Integer::MIN);
            let neg_one = Self::constant(-console::Integer::one());
            let overflows = self.is_equal(&min) & other.is_equal(&neg_one);
            Self::ternary(&overflows, &min, &signed_quotient)
        } else {
            // Ensure this is not a division by zero.
            E::assert(other.is_not_equal(&Self::zero()));

            // Eject the dividend and divisor, to compute the quotient as a witness.
            let dividend_value = self.eject_value();
            // TODO (howardwu): This bandaid was added on June 19, 2022 to prevent a panic when the divisor is 0.
            let divisor_value = match other.eject_value().is_zero() {
                true => match self.eject_value().is_zero() {
                    true => console::Integer::one(),
                    false => console::Integer::zero(),
                },
                false => other.eject_value(),
            };

            // Overflow is not possible for unsigned integers so we use wrapping operations.
            let quotient =
                Integer::new(Mode::Private, console::Integer::new(dividend_value.wrapping_div(&divisor_value)));
            let remainder =
                Integer::new(Mode::Private, console::Integer::new(dividend_value.wrapping_rem(&divisor_value)));

            // Ensure that Euclidean division holds for these values in the base field.
            E::assert_eq(self.to_field(), quotient.to_field() * other.to_field() + remainder.to_field());

            // Return the quotient of `self` and `other`.
            quotient
        }
    }
}

impl<E: Environment, I: IntegerType> Metrics<dyn DivWrapped<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        match I::is_signed() {
            true => match (case.0, case.1) {
                (Mode::Constant, Mode::Constant) => Count::is(I::BITS, 0, 0, 0),
                (Mode::Constant, _) | (_, Mode::Constant) => {
                    Count::less_than(6 * I::BITS, 0, (7 * I::BITS) + 10, (8 * I::BITS) + 16)
                }
                (_, _) => Count::is(5 * I::BITS, 0, (9 * I::BITS) + 10, (9 * I::BITS) + 16),
            },
            false => match (case.0, case.1) {
                (Mode::Constant, Mode::Constant) => Count::is(I::BITS, 0, 0, 0),
                (_, Mode::Constant) => Count::is(0, 0, 2 * I::BITS, (2 * I::BITS) + 1),
                (Mode::Constant, _) | (_, _) => Count::is(0, 0, (2 * I::BITS) + 1, (2 * I::BITS) + 2),
            },
        }
    }
}

impl<E: Environment, I: IntegerType> OutputMode<dyn DivWrapped<Integer<E, I>, Output = Integer<E, I>>>
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

    use core::{ops::RangeInclusive, panic::RefUnwindSafe};

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
        if second == console::Integer::zero() {
            check_operation_halts(&a, &b, Integer::div_wrapped);
        } else {
            let expected = first.wrapping_div(&second);
            Circuit::scope(name, || {
                let candidate = a.div_wrapped(&b);
                assert_eq!(expected, *candidate.eject_value());
                assert_eq!(console::Integer::new(expected), candidate.eject_value());
                assert_count!(DivWrapped(Integer<I>, Integer<I>) => Integer<I>, &(mode_a, mode_b));
                assert_output_mode!(DivWrapped(Integer<I>, Integer<I>) => Integer<I>, &(mode_a, mode_b), candidate);
            })
        }
        Circuit::reset();
    }

    fn run_test<I: IntegerType + RefUnwindSafe>(mode_a: Mode, mode_b: Mode) {
        for _ in 0..ITERATIONS {
            let first = Uniform::rand(&mut test_rng());
            let second = Uniform::rand(&mut test_rng());

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
