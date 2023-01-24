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

impl<E: Environment, I: IntegerType> SubFlagged<Self> for Integer<E, I> {
    type Output = (Self, Boolean<E>);

    #[inline]
    fn sub_flagged(&self, other: &Integer<E, I>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the difference and return the new constant.
            witness!(|self, other| {
                let (integer, overflow) = self.overflowing_sub(&other);
                (console::Integer::new(integer), overflow)
            })
        } else {
            // Instead of subtracting the bits of `self` and `other` directly, the integers are
            // converted into a field elements, and subtracted, before converting back to integers.
            // Note: This is safe as the field is larger than the maximum integer type supported.
            let difference = self.to_field() + (!other).to_field() + Field::one();

            // Extract the integer bits from the field element, with a carry bit.
            let (difference, carry) = match difference.to_lower_bits_le(I::BITS as usize + 1).split_last() {
                Some((carry, bits_le)) => (Integer::from_bits_le(bits_le), carry.clone()),
                // Note: `E::halt` should never be invoked as `I::BITS as usize + 1` is greater than zero.
                None => E::halt("Malformed difference detected during integer subtraction"),
            };

            // Compute the over/underflow flag.
            let flag = match I::is_signed() {
                // For signed subtraction, overflow and underflow conditions are:
                //   - a > 0 && b < 0 && a - b > 0 (Overflow)
                //   - a < 0 && b > 0 && a - b < 0 (Underflow)
                //   - Note: if sign(a) == sign(b) then over/underflow is impossible.
                //   - Note: the result of an overflow and underflow must be negative and positive, respectively.
                true => {
                    let is_different_signs = self.msb().is_not_equal(other.msb());
                    is_different_signs & difference.msb().is_equal(other.msb())
                }
                // For unsigned subtraction, overflow occurs if the carry bit is zero.
                false => !carry,
            };

            // Return the difference of `self` and `other` and the over/underflow `flag`.
            (difference, flag)
        }
    }
}

impl<E: Environment, I: IntegerType> Metrics<dyn SubFlagged<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        match I::is_signed() {
            true => match (case.0, case.1) {
                (Mode::Constant, Mode::Constant) => Count::is(I::BITS + 1, 0, 0, 0),
                (Mode::Constant, _) => Count::is(0, 0, I::BITS + 3, I::BITS + 4),
                (_, Mode::Constant) => Count::is(0, 0, I::BITS + 2, I::BITS + 3),
                (_, _) => Count::is(0, 0, I::BITS + 4, I::BITS + 5),
            },
            false => match (case.0, case.1) {
                (Mode::Constant, Mode::Constant) => Count::is(I::BITS + 1, 0, 0, 0),
                (_, _) => Count::is(0, 0, I::BITS + 1, I::BITS + 2),
            },
        }
    }
}

impl<E: Environment, I: IntegerType> OutputMode<dyn SubFlagged<Integer<E, I>, Output = Integer<E, I>>>
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

    fn check_sub<I: IntegerType>(
        name: &str,
        first: console::Integer<<Circuit as Environment>::Network, I>,
        second: console::Integer<<Circuit as Environment>::Network, I>,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::new(mode_b, second);
        let (expected_difference, expected_flag) = first.overflowing_sub(&second);
        Circuit::scope(name, || {
            let (candidate_difference, candidate_flag) = a.sub_flagged(&b);
            assert_eq!(expected_difference, *candidate_difference.eject_value());
            assert_eq!(expected_flag, candidate_flag.eject_value());
            assert_eq!(console::Integer::new(expected_difference), candidate_difference.eject_value());
            assert_count!(SubFlagged(Integer<I>, Integer<I>) => Integer<I>, &(mode_a, mode_b));
            assert_output_mode!(SubFlagged(Integer<I>, Integer<I>) => Integer<I>, &(mode_a, mode_b), candidate_difference);
        });
        Circuit::reset();
    }

    fn run_test<I: IntegerType + RefUnwindSafe>(mode_a: Mode, mode_b: Mode) {
        let mut rng = TestRng::default();

        for i in 0..ITERATIONS {
            let name = format!("Sub: {} - {} {}", mode_a, mode_b, i);
            let first = Uniform::rand(&mut rng);
            let second = Uniform::rand(&mut rng);
            check_sub::<I>(&name, first, second, mode_a, mode_b);
        }

        // Overflow
        if I::is_signed() {
            check_sub::<I>("MAX - (-1)", console::Integer::MAX, -console::Integer::one(), mode_a, mode_b);
        }
        // Underflow
        check_sub::<I>("MIN - 1", console::Integer::MIN, console::Integer::one(), mode_a, mode_b);
    }

    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe>(mode_a: Mode, mode_b: Mode)
    where
        RangeInclusive<I>: Iterator<Item = I>,
    {
        for first in I::MIN..=I::MAX {
            for second in I::MIN..=I::MAX {
                let first = console::Integer::<_, I>::new(first);
                let second = console::Integer::<_, I>::new(second);

                let name = format!("Sub: ({} - {})", first, second);
                check_sub::<I>(&name, first, second, mode_a, mode_b);
            }
        }
    }

    test_integer_binary!(run_test, i8, minus);
    test_integer_binary!(run_test, i16, minus);
    test_integer_binary!(run_test, i32, minus);
    test_integer_binary!(run_test, i64, minus);
    test_integer_binary!(run_test, i128, minus);

    test_integer_binary!(run_test, u8, minus);
    test_integer_binary!(run_test, u16, minus);
    test_integer_binary!(run_test, u32, minus);
    test_integer_binary!(run_test, u64, minus);
    test_integer_binary!(run_test, u128, minus);

    test_integer_binary!(#[ignore], run_exhaustive_test, u8, minus, exhaustive);
    test_integer_binary!(#[ignore], run_exhaustive_test, i8, minus, exhaustive);
}
