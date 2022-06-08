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

impl<E: Environment, I: IntegerType> Equal<Self> for Integer<E, I> {
    type Output = Boolean<E>;

    ///
    /// Returns `true` if `self` and `other` are equal.
    ///
    fn is_equal(&self, other: &Self) -> Self::Output {
        // Determine if this operation is constant or variable.
        match self.is_constant() && other.is_constant() {
            true => self
                .bits_le
                .iter()
                .zip_eq(other.bits_le.iter())
                .map(|(this, that)| this.is_equal(that))
                .fold(Boolean::constant(true), |a, b| a & b),
            false => {
                // Instead of comparing the bits of `self` and `other` directly, the integers are
                // converted into a field elements, and checked if they are equivalent as field elements.
                // Note: This is safe as the field is larger than the maximum integer type supported.
                self.to_field().is_equal(&other.to_field())
            }
        }
    }

    ///
    /// Returns `true` if `self` and `other` are *not* equal.
    ///
    /// This method constructs a boolean that indicates if
    /// `self` and `other ` are *not* equal to each other.
    ///
    fn is_not_equal(&self, other: &Self) -> Self::Output {
        !self.is_equal(other)
    }
}

impl<E: Environment, I: IntegerType> Metrics<dyn Equal<Integer<E, I>, Output = Boolean<E>>> for Integer<E, I> {
    type Case = (Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        match case.0.is_constant() && case.1.is_constant() {
            true => Count::is(0, 0, 0, 0),
            false => Count::is(0, 0, 2, 3),
        }
    }
}

impl<E: Environment, I: IntegerType> OutputMode<dyn Equal<Integer<E, I>, Output = Boolean<E>>> for Integer<E, I> {
    type Case = (Mode, Mode);

    fn output_mode(case: &Self::Case) -> Mode {
        match case.0.is_constant() && case.1.is_constant() {
            true => Mode::Constant,
            false => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    use std::ops::RangeInclusive;

    const ITERATIONS: u64 = 100;

    fn check_equals<I: IntegerType>(
        name: &str,
        first: console::Integer<<Circuit as Environment>::Network, I>,
        second: console::Integer<<Circuit as Environment>::Network, I>,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let expected = first == second;
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);
        Circuit::scope(name, || {
            let candidate = a.is_equal(&b);
            assert_eq!(expected, candidate.eject_value());
            assert_count!(Equal(Integer<I>, Integer<I>) => Boolean, &(mode_a, mode_b));
            assert_output_mode!(Equal(Integer<I>, Integer<I>) => Boolean, &(mode_a, mode_b), candidate);
        });
        Circuit::reset();
    }

    fn run_test<I: IntegerType>(mode_a: Mode, mode_b: Mode) {
        for i in 0..ITERATIONS {
            let first = Uniform::rand(&mut test_rng());
            let second = Uniform::rand(&mut test_rng());

            let name = format!("Eq: {} == {} {}", mode_a, mode_b, i);
            check_equals::<I>(&name, first, second, mode_a, mode_b);
            check_equals::<I>(&name, second, first, mode_a, mode_b); // Commute the operation.
        }
    }

    fn run_exhaustive_test<I: IntegerType>(mode_a: Mode, mode_b: Mode)
    where
        RangeInclusive<I>: Iterator<Item = I>,
    {
        for first in I::MIN..=I::MAX {
            for second in I::MIN..=I::MAX {
                let first = console::Integer::<_, I>::new(first);
                let second = console::Integer::<_, I>::new(second);

                let name = format!("Equals: ({} == {})", first, second);
                check_equals::<I>(&name, first, second, mode_a, mode_b);
            }
        }
    }

    test_integer_binary!(run_test, i8, equals);
    test_integer_binary!(run_test, i16, equals);
    test_integer_binary!(run_test, i32, equals);
    test_integer_binary!(run_test, i64, equals);
    test_integer_binary!(run_test, i128, equals);

    test_integer_binary!(run_test, u8, equals);
    test_integer_binary!(run_test, u16, equals);
    test_integer_binary!(run_test, u32, equals);
    test_integer_binary!(run_test, u64, equals);
    test_integer_binary!(run_test, u128, equals);

    test_integer_binary!(#[ignore], run_exhaustive_test, u8, equals, exhaustive);
    test_integer_binary!(#[ignore], run_exhaustive_test, i8, equals, exhaustive);
}
