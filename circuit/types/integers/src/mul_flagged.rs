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

impl<E: Environment, I: IntegerType> MulFlagged<Self> for Integer<E, I> {
    type Output = (Self, Boolean<E>);

    #[inline]
    fn mul_flagged(&self, other: &Integer<E, I>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the product and flag and return them as constants.
            witness!(|self, other| {
                let (product, flag) = self.overflowing_mul(&other);
                (console::Integer::new(product), flag)
            })
        } else if I::is_signed() {
            // Multiply the absolute value of `self` and `other` in the base field.
            // Note that it is safe to use abs_wrapped since we want Integer::MIN to be interpreted as an unsigned number.
            let (product, carry) = Self::mul_with_carry(&self.abs_wrapped(), &other.abs_wrapped());

            // We need to check that the abs(a) * abs(b) did not exceed the unsigned maximum.
            let carry_bits_nonzero = carry.iter().fold(Boolean::constant(false), |a, b| a | b);

            // If the product should be positive, then it cannot exceed the signed maximum.
            let operands_same_sign = &self.msb().is_equal(other.msb());
            let positive_product_overflows = operands_same_sign & product.msb();

            // If the product should be negative, then it cannot exceed the absolute value of the signed minimum.
            let negative_product_underflows = {
                let lower_product_bits_nonzero =
                    product.bits_le[..(I::BITS as usize - 1)].iter().fold(Boolean::constant(false), |a, b| a | b);
                let negative_product_lt_or_eq_signed_min =
                    !product.msb() | (product.msb() & !lower_product_bits_nonzero);
                !operands_same_sign & !negative_product_lt_or_eq_signed_min
            };

            // Compute the overflow flag.
            let overflow = carry_bits_nonzero | positive_product_overflows | negative_product_underflows;

            // Return the product of `self` and `other` with the appropriate sign, and the overflow flag.
            (Self::ternary(operands_same_sign, &product, &Self::zero().sub_wrapped(&product)), overflow)
        } else {
            // Compute the product of `self` and `other`.
            let (product, carry) = Self::mul_with_carry(self, other);

            // For unsigned multiplication, an overflow occurs if any of the carry bits are set.
            let overflow = carry.iter().fold(Boolean::constant(false), |a, b| a | b);

            // Return the product of `self` and `other` and the overflow flag.
            (product, overflow)
        }
    }
}

impl<E: Environment, I: IntegerType> Metrics<dyn MulFlagged<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        // Case 1 - 2 integers fit in 1 field element (u8, u16, u32, u64, i8, i16, i32, i64).
        if 2 * I::BITS < (E::BaseField::size_in_bits() - 1) as u64 {
            match I::is_signed() {
                // Signed case
                true => match (case.0, case.1) {
                    (Mode::Constant, Mode::Constant) => Count::is(I::BITS + 1, 0, 0, 0),
                    (Mode::Constant, _) | (_, Mode::Constant) => {
                        Count::is(4 * I::BITS, 0, (8 * I::BITS) + 5, (8 * I::BITS) + 8)
                    }
                    (_, _) => Count::is(3 * I::BITS, 0, (10 * I::BITS) + 8, (10 * I::BITS) + 12),
                },
                // Unsigned case
                false => match (case.0, case.1) {
                    (Mode::Constant, Mode::Constant) => Count::is(I::BITS + 1, 0, 0, 0),
                    (Mode::Constant, _) | (_, Mode::Constant) => Count::is(0, 0, (3 * I::BITS) - 1, 3 * I::BITS),
                    (_, _) => Count::is(0, 0, 3 * I::BITS, (3 * I::BITS) + 1),
                },
            }
        }
        // Case 2 - 1.5 integers fit in 1 field element (u128, i128).
        else if (I::BITS + I::BITS / 2) < (E::BaseField::size_in_bits() - 1) as u64 {
            match I::is_signed() {
                // Signed case
                true => match (case.0, case.1) {
                    (Mode::Constant, Mode::Constant) => Count::is(I::BITS + 1, 0, 0, 0),
                    (Mode::Constant, _) | (_, Mode::Constant) => {
                        Count::is(4 * I::BITS, 0, (9 * I::BITS) + 7, (9 * I::BITS) + 11)
                    }
                    (_, _) => Count::is(3 * I::BITS, 0, (11 * I::BITS) + 13, (11 * I::BITS) + 18),
                },
                // Unsigned case
                false => match (case.0, case.1) {
                    (Mode::Constant, Mode::Constant) => Count::is(I::BITS + 1, 0, 0, 0),
                    (Mode::Constant, _) | (_, Mode::Constant) => Count::is(0, 0, (4 * I::BITS) + 1, (4 * I::BITS) + 3),
                    (_, _) => Count::is(0, 0, (4 * I::BITS) + 5, (4 * I::BITS) + 7),
                },
            }
        } else {
            E::halt(format!("Multiplication of integers of size {} is not supported", I::BITS))
        }
    }
}

impl<E: Environment, I: IntegerType> OutputMode<dyn MulFlagged<Integer<E, I>, Output = Integer<E, I>>>
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

    fn check_mul<I: IntegerType + RefUnwindSafe>(
        name: &str,
        first: console::Integer<<Circuit as Environment>::Network, I>,
        second: console::Integer<<Circuit as Environment>::Network, I>,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);

        // Check that the flagged implementation produces the correct result.
        let (expected_result, expected_flag) = first.overflowing_mul(&second);
        Circuit::scope(name, || {
            let (candidate_result, candidate_flag) = a.mul_flagged(&b);
            assert_eq!(expected_result, *candidate_result.eject_value());
            assert_eq!(expected_flag, candidate_flag.eject_value());
            assert_eq!(console::Integer::new(expected_result), candidate_result.eject_value());
            assert_count!(MulFlagged(Integer<I>, Integer<I>) => Integer<I>, &(mode_a, mode_b));
            assert_output_mode!(MulFlagged(Integer<I>, Integer<I>) => Integer<I>, &(mode_a, mode_b), candidate_result);
        });
        Circuit::reset();

        let (flagged_result, flag) = (&a).mul_flagged(&b);

        // Check that the flagged implementation matches wrapped implementation.
        let wrapped_result = (&a).mul_wrapped(&b);
        assert_eq!(flagged_result.eject_value(), wrapped_result.eject_value());

        // Check that the flagged implementation matches the checked implementation.
        match (flag.eject_value(), mode_a, mode_b) {
            // If the flag is set and the mode is constant, the checked implementation should halt.
            (true, Mode::Constant, Mode::Constant) => check_operation_halts(&a, &b, Integer::mul_checked),
            _ => {
                Circuit::scope(name, || {
                    let checked_result = a.mul_checked(&b);
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

        for i in 0..ITERATIONS {
            // TODO (@pranav) Uniform random sampling almost always produces arguments that result in an overflow.
            //  Is there a better method for sampling arguments?
            let first = Uniform::rand(&mut rng);
            let second = Uniform::rand(&mut rng);

            let name = format!("Mul: {} * {} {}", mode_a, mode_b, i);
            check_mul::<I>(&name, first, second, mode_a, mode_b);
            check_mul::<I>(&name, second, first, mode_a, mode_b); // Commute the operation.

            let name = format!("Double: {} * {} {}", mode_a, mode_b, i);
            check_mul::<I>(&name, first, console::Integer::one() + console::Integer::one(), mode_a, mode_b);
            check_mul::<I>(&name, console::Integer::one() + console::Integer::one(), first, mode_a, mode_b); // Commute the operation.

            let name = format!("Square: {} * {} {}", mode_a, mode_b, i);
            check_mul::<I>(&name, first, first, mode_a, mode_b);
        }

        // Check specific cases common to signed and unsigned integers.
        check_mul::<I>("1 * MAX", console::Integer::one(), console::Integer::MAX, mode_a, mode_b);
        check_mul::<I>("MAX * 1", console::Integer::MAX, console::Integer::one(), mode_a, mode_b);
        check_mul::<I>("1 * MIN", console::Integer::one(), console::Integer::MIN, mode_a, mode_b);
        check_mul::<I>("MIN * 1", console::Integer::MIN, console::Integer::one(), mode_a, mode_b);
        check_mul::<I>("0 * MAX", console::Integer::zero(), console::Integer::MAX, mode_a, mode_b);
        check_mul::<I>("MAX * 0", console::Integer::MAX, console::Integer::zero(), mode_a, mode_b);
        check_mul::<I>("0 * MIN", console::Integer::zero(), console::Integer::MIN, mode_a, mode_b);
        check_mul::<I>("MIN * 0", console::Integer::MIN, console::Integer::zero(), mode_a, mode_b);
        check_mul::<I>("1 * 1", console::Integer::one(), console::Integer::one(), mode_a, mode_b);

        // Check common overflow cases.
        check_mul::<I>(
            "MAX * 2",
            console::Integer::MAX,
            console::Integer::one() + console::Integer::one(),
            mode_a,
            mode_b,
        );
        check_mul::<I>(
            "2 * MAX",
            console::Integer::one() + console::Integer::one(),
            console::Integer::MAX,
            mode_a,
            mode_b,
        );

        // Check additional corner cases for signed integers.
        if I::is_signed() {
            check_mul::<I>("MAX * -1", console::Integer::MAX, -console::Integer::one(), mode_a, mode_b);
            check_mul::<I>("-1 * MAX", -console::Integer::one(), console::Integer::MAX, mode_a, mode_b);
            check_mul::<I>("MIN * -1", console::Integer::MIN, -console::Integer::one(), mode_a, mode_b);
            check_mul::<I>("-1 * MIN", -console::Integer::one(), console::Integer::MIN, mode_a, mode_b);
            check_mul::<I>(
                "MIN * -2",
                console::Integer::MIN,
                -console::Integer::one() - console::Integer::one(),
                mode_a,
                mode_b,
            );
            check_mul::<I>(
                "-2 * MIN",
                -console::Integer::one() - console::Integer::one(),
                console::Integer::MIN,
                mode_a,
                mode_b,
            );
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

                let name = format!("Mul: ({} * {})", first, second);
                check_mul::<I>(&name, first, second, mode_a, mode_b);
            }
        }
    }

    test_integer_binary!(run_test, i8, times);
    test_integer_binary!(run_test, i16, times);
    test_integer_binary!(run_test, i32, times);
    test_integer_binary!(run_test, i64, times);
    test_integer_binary!(run_test, i128, times);

    test_integer_binary!(run_test, u8, times);
    test_integer_binary!(run_test, u16, times);
    test_integer_binary!(run_test, u32, times);
    test_integer_binary!(run_test, u64, times);
    test_integer_binary!(run_test, u128, times);

    test_integer_binary!(#[ignore], run_exhaustive_test, u8, times, exhaustive);
    test_integer_binary!(#[ignore], run_exhaustive_test, i8, times, exhaustive);
}
