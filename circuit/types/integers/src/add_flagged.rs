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

impl<E: Environment, I: IntegerType> AddFlagged<Self> for Integer<E, I> {
    type Output = (Self, Boolean<E>);

    #[inline]
    fn add_flagged(&self, other: &Integer<E, I>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the sum and return the new constant.
            witness!(|self, other| {
                let (integer, overflow) = self.overflowing_add(&other);
                (console::Integer::new(integer), overflow)
            })
        } else {
            // Instead of adding the bits of `self` and `other` directly, the integers are
            // converted into a field elements, and summed, before converting back to integers.
            // Note: This is safe as the field is larger than the maximum integer type supported.
            let sum = self.to_field() + other.to_field();

            // Extract the integer bits from the field element, with a carry bit.
            let (sum, carry) = match sum.to_lower_bits_le(I::BITS as usize + 1).split_last() {
                Some((carry, bits_le)) => (Integer::from_bits_le(bits_le), carry.clone()),
                // Note: `E::halt` should never be invoked as `I::BITS as usize + 1` is greater than zero.
                None => E::halt("Malformed sum detected during integer addition"),
            };

            // Check for overflow.
            let is_overflow = match I::is_signed() {
                // For signed addition, overflow and underflow conditions are:
                //   - a > 0 && b > 0 && a + b < 0 (Overflow)
                //   - a < 0 && b < 0 && a + b > 0 (Underflow)
                //   - Note: if sign(a) != sign(b) then over/underflow is impossible.
                //   - Note: the result of an overflow and underflow must be negative and positive, respectively.
                true => {
                    let is_same_sign = self.msb().is_equal(other.msb());
                    is_same_sign & sum.msb().is_not_equal(self.msb())
                }
                // For unsigned addition, return the carry bit.
                false => carry,
            };

            // Return the sum of `self` and `other` and the `is_overflow` flag
            (sum, is_overflow)
        }
    }
}

impl<E: Environment, I: IntegerType> Metrics<dyn AddFlagged<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        match I::is_signed() {
            true => match (case.0, case.1) {
                (Mode::Constant, Mode::Constant) => Count::is(I::BITS + 1, 0, 0, 0),
                (Mode::Constant, _) => Count::is(0, 0, I::BITS + 2, I::BITS + 3),
                (_, Mode::Constant) => Count::is(0, 0, I::BITS + 3, I::BITS + 4),
                (_, _) => Count::is(0, 0, I::BITS + 4, I::BITS + 5),
            },
            false => match (case.0, case.1) {
                (Mode::Constant, Mode::Constant) => Count::is(I::BITS + 1, 0, 0, 0),
                (_, _) => Count::is(0, 0, I::BITS + 1, I::BITS + 2),
            },
        }
    }
}

impl<E: Environment, I: IntegerType> OutputMode<dyn AddFlagged<Integer<E, I>, Output = Integer<E, I>>>
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

    const ITERATIONS: u64 = 128;

    fn check_add<I: IntegerType + RefUnwindSafe>(
        name: &str,
        first: console::Integer<<Circuit as Environment>::Network, I>,
        second: console::Integer<<Circuit as Environment>::Network, I>,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::new(mode_b, second);

        // Check that the flagged implementation produces the correct result.
        let (expected_sum, expected_flag) = first.overflowing_add(&second);
        Circuit::scope(name, || {
            let (candidate_sum, candidate_flag) = a.add_flagged(&b);
            assert_eq!(expected_sum, *candidate_sum.eject_value());
            assert_eq!(expected_flag, candidate_flag.eject_value());
            assert_eq!(console::Integer::new(expected_sum), candidate_sum.eject_value());
            assert_count!(AddFlagged(Integer<I>, Integer<I>) => Integer<I>, &(mode_a, mode_b));
            assert_output_mode!(AddFlagged(Integer<I>, Integer<I>) => Integer<I>, &(mode_a, mode_b), candidate_sum);
        });
        Circuit::reset();

        let (flagged_result, flag) = (&a).add_flagged(&b);

        // Check that the flagged implementation matches wrapped implementation.
        let wrapped_result = (&a).add_wrapped(&b);
        assert_eq!(flagged_result.eject_value(), wrapped_result.eject_value());

        // Check that the flagged implementation matches the checked implementation.
        match (flag.eject_value(), mode_a, mode_b) {
            // If the flag is set and the mode is constant, the checked implementation should halt.
            (true, Mode::Constant, Mode::Constant) => check_operation_halts(&a, &b, Integer::add_checked),
            _ => {
                Circuit::scope(name, || {
                    let checked_result = a.add_checked(&b);
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
            let first = Uniform::rand(&mut rng);
            let second = Uniform::rand(&mut rng);

            let name = format!("Add: {} + {} {}", mode_a, mode_b, i);
            check_add::<I>(&name, first, second, mode_a, mode_b);
            check_add::<I>(&name, second, first, mode_a, mode_b); // Commute the operation.
        }

        // Overflow
        check_add::<I>("MAX + 1", console::Integer::MAX, console::Integer::one(), mode_a, mode_b);
        check_add::<I>("1 + MAX", console::Integer::one(), console::Integer::MAX, mode_a, mode_b);

        // Underflow
        if I::is_signed() {
            check_add::<I>("MIN + (-1)", console::Integer::MIN, -console::Integer::one(), mode_a, mode_b);
            check_add::<I>("-1 + MIN", -console::Integer::one(), console::Integer::MIN, mode_a, mode_b);
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

                let name = format!("Add: ({} + {})", first, second);
                check_add::<I>(&name, first, second, mode_a, mode_b);
            }
        }
    }

    test_integer_binary!(run_test, i8, plus);
    test_integer_binary!(run_test, i16, plus);
    test_integer_binary!(run_test, i32, plus);
    test_integer_binary!(run_test, i64, plus);
    test_integer_binary!(run_test, i128, plus);

    test_integer_binary!(run_test, u8, plus);
    test_integer_binary!(run_test, u16, plus);
    test_integer_binary!(run_test, u32, plus);
    test_integer_binary!(run_test, u64, plus);
    test_integer_binary!(run_test, u128, plus);

    test_integer_binary!(#[ignore], run_exhaustive_test, u8, plus, exhaustive);
    test_integer_binary!(#[ignore], run_exhaustive_test, i8, plus, exhaustive);
}
