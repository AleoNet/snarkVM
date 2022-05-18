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

impl<E: Environment, I: IntegerType> GreaterThan<Self> for Integer<E, I> {
    type Output = Boolean<E>;

    /// Returns `true` if `self` is greater than `other`.
    fn is_greater_than(&self, other: &Self) -> Self::Output {
        other.is_less_than(self)
    }
}

impl<E: Environment, I: IntegerType> Metadata<dyn GreaterThan<Integer<E, I>, Output = Boolean<E>>> for Integer<E, I> {
    type Case = (IntegerCircuitType<E, I>, IntegerCircuitType<E, I>);
    type OutputType = CircuitType<Boolean<E>>;

    fn count(case: &Self::Case) -> Count {
        match I::is_signed() {
            true => match (case.0.eject_mode(), case.1.eject_mode()) {
                (Mode::Constant, Mode::Constant) => Count::is(1, 0, 0, 0),
                (Mode::Constant, _) | (_, Mode::Constant) => Count::is(I::BITS, 0, I::BITS + 2, I::BITS + 3),
                (_, _) => Count::is(I::BITS, 0, I::BITS + 4, I::BITS + 5),
            },
            false => match case.0.is_constant() && case.1.is_constant() {
                true => Count::is(1, 0, 0, 0),
                false => Count::is(I::BITS, 0, I::BITS + 1, I::BITS + 2),
            },
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        let (lhs, rhs) = case;
        output_type!(Self, LessThan<Self, Output = Boolean<E>>, (rhs, lhs))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    use std::ops::RangeInclusive;

    const ITERATIONS: u64 = 100;

    fn check_is_greater_than<I: IntegerType>(name: &str, first: I, second: I, mode_a: Mode, mode_b: Mode) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);

        // Check `is_greater_than`
        let expected = first > second;
        Circuit::scope(name, || {
            let candidate = a.is_greater_than(&b);
            assert_eq!(expected, candidate.eject_value());

            let case = (IntegerCircuitType::from(&a), IntegerCircuitType::from(&b));
            assert_count!(GreaterThan(Integer<I>, Integer<I>) => Boolean, &case);
            assert_output_type!(GreaterThan(Integer<I>, Integer<I>) => Boolean, case, candidate);
        });
        Circuit::reset();
    }

    fn run_test<I: IntegerType>(mode_a: Mode, mode_b: Mode) {
        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut test_rng());
            let second: I = UniformRand::rand(&mut test_rng());

            let name = format!("GreaterThan: ({}, {}) - {}th iteration", mode_a, mode_b, i);
            check_is_greater_than(&name, first, second, mode_a, mode_b);
        }
    }

    fn run_exhaustive_test<I: IntegerType>(mode_a: Mode, mode_b: Mode)
    where
        RangeInclusive<I>: Iterator<Item = I>,
    {
        for first in I::MIN..=I::MAX {
            for second in I::MIN..=I::MAX {
                let name = format!("GreaterThan: ({}, {})", first, second);
                check_is_greater_than(&name, first, second, mode_a, mode_b);
            }
        }
    }

    test_integer_binary!(run_test, i8, is_greater_than);
    test_integer_binary!(run_test, i16, is_greater_than);
    test_integer_binary!(run_test, i32, is_greater_than);
    test_integer_binary!(run_test, i64, is_greater_than);
    test_integer_binary!(run_test, i128, is_greater_than);

    test_integer_binary!(run_test, u8, is_greater_than);
    test_integer_binary!(run_test, u16, is_greater_than);
    test_integer_binary!(run_test, u32, is_greater_than);
    test_integer_binary!(run_test, u64, is_greater_than);
    test_integer_binary!(run_test, u128, is_greater_than);

    test_integer_binary!(#[ignore], run_exhaustive_test, u8, is_greater_than, exhaustive);
    test_integer_binary!(#[ignore], run_exhaustive_test, i8, is_greater_than, exhaustive);
}
