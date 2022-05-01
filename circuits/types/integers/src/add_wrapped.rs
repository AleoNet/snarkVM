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

impl<E: Environment, I: IntegerType> AddWrapped<Self> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn add_wrapped(&self, other: &Integer<E, I>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the sum and return the new constant.
            Integer::new(Mode::Constant, self.eject_value().wrapping_add(&other.eject_value()))
        } else {
            // Instead of adding the bits of `self` and `other` directly, the integers are
            // converted into a field elements, and summed, before converting back to integers.
            // Note: This is safe as the field is larger than the maximum integer type supported.
            let sum = self.to_field() + other.to_field();

            // Extract the integer bits from the field element, with a carry bit.
            let mut bits_le = sum.to_lower_bits_le(I::BITS as usize + 1);
            // Drop the carry bit as the operation is wrapped addition.
            bits_le.pop();

            // Return the sum of `self` and `other`.
            Integer { bits_le, phantom: Default::default() }
        }
    }
}

impl<E: Environment, I: IntegerType> Metrics<dyn AddWrapped<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        match (case.0, case.1) {
            (Mode::Constant, Mode::Constant) => Count::is(I::BITS, 0, 0, 0),
            (_, _) => Count::is(0, 0, I::BITS + 1, I::BITS + 2),
        }
    }
}

impl<E: Environment, I: IntegerType> OutputMode<dyn AddWrapped<Integer<E, I>, Output = Integer<E, I>>>
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

    use core::ops::RangeInclusive;

    const ITERATIONS: usize = 128;

    fn check_add<I: IntegerType>(name: &str, first: I, second: I, mode_a: Mode, mode_b: Mode) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::new(mode_b, second);
        let expected = first.wrapping_add(&second);
        Circuit::scope(name, || {
            let candidate = a.add_wrapped(&b);
            assert_eq!(expected, candidate.eject_value());
            assert_count!(Integer<Circuit, I>, AddWrapped<Integer<Circuit, I>, Output=Integer<Circuit, I>>, &(mode_a, mode_b));
            assert_output_mode!(candidate, Integer<Circuit, I>, AddWrapped<Integer<Circuit, I>, Output=Integer<Circuit, I>>, &(mode_a, mode_b));
        });
        Circuit::reset();
    }

    fn run_test<I: IntegerType>(mode_a: Mode, mode_b: Mode) {
        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut test_rng());
            let second: I = UniformRand::rand(&mut test_rng());

            let name = format!("Add: {} + {} {}", mode_a, mode_b, i);
            check_add(&name, first, second, mode_a, mode_b);
            check_add(&name, second, first, mode_a, mode_b); // Commute the operation.
        }

        // Overflow
        check_add("MAX + 1", I::MAX, I::one(), mode_a, mode_b);
        check_add("1 + MAX", I::one(), I::MAX, mode_a, mode_b);

        // Underflow
        if I::is_signed() {
            check_add("MIN + (-1)", I::MIN, I::zero() - I::one(), mode_a, mode_b);
            check_add("-1 + MIN", I::zero() - I::one(), I::MIN, mode_a, mode_b);
        }
    }

    fn run_exhaustive_test<I: IntegerType>(mode_a: Mode, mode_b: Mode)
    where
        RangeInclusive<I>: Iterator<Item = I>,
    {
        for first in I::MIN..=I::MAX {
            for second in I::MIN..=I::MAX {
                let name = format!("Add: ({} + {})", first, second);
                check_add(&name, first, second, mode_a, mode_b);
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
