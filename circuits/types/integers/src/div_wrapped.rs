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
        // Halt on division by zero as there is no sound way to perform
        // this operation.
        if other.eject_value().is_zero() {
            E::halt("Division by zero error")
        }

        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the quotient and return the new constant.
            Integer::new(Mode::Constant, self.eject_value().wrapping_div(&other.eject_value()))
        } else if I::is_signed() {
            // Divide the absolute value of `self` and `other` in the base field.
            let unsigned_dividend = self.abs_wrapped().cast_as_dual();
            let unsigned_divisor = other.abs_wrapped().cast_as_dual();
            let unsigned_quotient = unsigned_dividend.div_wrapped(&unsigned_divisor);

            // TODO (@pranav) Do we need to check that the quotient cannot exceed abs(I::MIN)?
            //  This is implicitly true since the dividend <= abs(I::MIN) and 0 <= quotient <= dividend.
            let signed_quotient = Self { bits_le: unsigned_quotient.bits_le, phantom: Default::default() };
            let operands_same_sign = &self.msb().is_equal(other.msb());
            let signed_quotient =
                Self::ternary(operands_same_sign, &signed_quotient, &Self::zero().sub_wrapped(&signed_quotient));

            // Signed integer division wraps when the dividend is I::MIN and the divisor is -1.
            let min = Self::constant(I::MIN);
            let neg_one = Self::constant(I::zero() - I::one());
            let overflows = self.is_equal(&min) & other.is_equal(&neg_one);
            Self::ternary(&overflows, &min, &signed_quotient)
        } else {
            // Eject the dividend and divisor, to compute the quotient as a witness.
            let dividend_value = self.eject_value();
            let divisor_value = other.eject_value();

            // Overflow is not possible for unsigned integers so we use wrapping operations.
            let quotient = Integer::new(Mode::Private, dividend_value.wrapping_div(&divisor_value));
            let remainder = Integer::new(Mode::Private, dividend_value.wrapping_rem(&divisor_value));

            // Ensure that Euclidean division holds for these values in the base field.
            E::assert_eq(self.to_field(), quotient.to_field() * other.to_field() + remainder.to_field());

            // Return the quotient of `self` and `other`.
            quotient
        }
    }
}

impl<E: Environment, I: IntegerType> Metadata<dyn DivWrapped<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (CircuitType<Self>, CircuitType<Self>);
    type OutputType = CircuitType<Self>;

    fn count(case: &Self::Case) -> Count {
        match I::is_signed() {
            true => match case {
                (CircuitType::Constant(_), CircuitType::Constant(_)) => Count::is(I::BITS, 0, 0, 0),
                // (_, _) => {
                //     // // Divide the absolute value of `self` and `other` in the base field.
                //     // let unsigned_dividend = self.abs_wrapped().cast_as_dual();
                //     // let unsigned_divisor = other.abs_wrapped().cast_as_dual();
                //     // let unsigned_quotient = unsigned_dividend.div_wrapped(&unsigned_divisor);
                //     //
                //     // // TODO (@pranav) Do we need to check that the quotient cannot exceed abs(I::MIN)?
                //     // //  This is implicitly true since the dividend <= abs(I::MIN) and 0 <= quotient <= dividend.
                //     // let signed_quotient = Self { bits_le: unsigned_quotient.bits_le, phantom: Default::default() };
                //     // let operands_same_sign = &self.msb().is_equal(other.msb());
                //     // let signed_quotient = Self::ternary(
                //     //     operands_same_sign,
                //     //     &signed_quotient,
                //     //     &Self::zero().sub_wrapped(&signed_quotient),
                //     // );
                //     //
                //     // // Signed integer division wraps when the dividend is I::MIN and the divisor is -1.
                //     // let min = Self::constant(I::MIN);
                //     // let neg_one = Self::constant(I::zero() - I::one());
                //     // let overflows = self.is_equal(&min) & other.is_equal(&neg_one);
                //     // Self::ternary(&overflows, &min, &signed_quotient)
                //     todo!()
                // }
                (CircuitType::Constant(_), _) | (_, CircuitType::Constant(_)) => {
                    Count::is(6 * I::BITS, 0, (7 * I::BITS) + 10, (8 * I::BITS) + 16)
                }
                (_, _) => Count::is(5 * I::BITS, 0, (9 * I::BITS) + 10, (9 * I::BITS) + 16),
            },
            false => match case {
                (CircuitType::Constant(_), CircuitType::Constant(_)) => Count::is(I::BITS, 0, 0, 0),
                (_, CircuitType::Constant(_)) => Count::is(0, 0, 2 * I::BITS, (2 * I::BITS) + 1),
                (CircuitType::Constant(_), _) | (_, _) => Count::is(0, 0, (2 * I::BITS) + 1, (2 * I::BITS) + 2),
            },
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case {
            (CircuitType::Constant(a), CircuitType::Constant(b)) => {
                CircuitType::from(a.circuit().div_wrapped(&b.circuit()))
            }
            (_, _) => CircuitType::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};
    use test_utilities::*;

    use core::{ops::RangeInclusive, panic::RefUnwindSafe};

    const ITERATIONS: u64 = 32;

    fn check_div<I: IntegerType + RefUnwindSafe>(name: &str, first: I, second: I, mode_a: Mode, mode_b: Mode) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);
        if second == I::zero() {
            check_operation_halts(&a, &b, Integer::div_wrapped);
        } else {
            let expected = first.wrapping_div(&second);
            Circuit::scope(name, || {
                let candidate = a.div_wrapped(&b);
                assert_eq!(expected, candidate.eject_value());

                let case = (CircuitType::from(a), CircuitType::from(b));
                assert_count!(DivWrapped(Integer<I>, Integer<I>) => Integer<I>, &case);
                assert_output_type!(DivWrapped(Integer<I>, Integer<I>) => Integer<I>, case, candidate);
            })
        }
        Circuit::reset();
    }

    fn run_test<I: IntegerType + RefUnwindSafe>(mode_a: Mode, mode_b: Mode) {
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
