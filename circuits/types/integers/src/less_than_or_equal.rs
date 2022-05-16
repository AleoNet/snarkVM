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

impl<E: Environment, I: IntegerType> LessThanOrEqual<Self> for Integer<E, I> {
    type Output = Boolean<E>;

    /// Returns `true` if `self` is less than or equal to `other`.
    fn is_less_than_or_equal(&self, other: &Self) -> Self::Output {
        other.is_greater_than_or_equal(self)
    }
}

impl<E: Environment, I: IntegerType> Metadata<dyn LessThanOrEqual<Integer<E, I>, Output = Boolean<E>>>
    for Integer<E, I>
{
    type Case = (CircuitType<Self>, CircuitType<Self>);
    type OutputType = CircuitType<Boolean<E>>;

    fn count(case: &Self::Case) -> Count {
        match I::is_signed() {
            true => match case {
                (CircuitType::Constant(_), CircuitType::Constant(_)) => Count::is(1, 0, 0, 0),
                (CircuitType::Constant(_), _) | (_, CircuitType::Constant(_)) => {
                    Count::is(I::BITS, 0, I::BITS + 2, I::BITS + 3)
                }
                (_, _) => Count::is(I::BITS, 0, I::BITS + 4, I::BITS + 5),
            },
            false => match case {
                (CircuitType::Constant(_), CircuitType::Constant(_)) => Count::is(1, 0, 0, 0),
                (_, _) => Count::is(I::BITS, 0, I::BITS + 1, I::BITS + 2),
            },
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case {
            (CircuitType::Constant(a), CircuitType::Constant(b)) => {
                CircuitType::from(a.circuit().is_less_than_or_equal(&b.circuit()))
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

    use std::ops::RangeInclusive;

    const ITERATIONS: u64 = 100;

    fn check_is_less_than_or_equal<I: IntegerType>(name: &str, first: I, second: I, mode_a: Mode, mode_b: Mode) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);

        // Check `is_less_than_or_equal`
        let expected = first <= second;
        Circuit::scope(name, || {
            let candidate = a.is_less_than_or_equal(&b);
            assert_eq!(expected, candidate.eject_value());

            let case = (CircuitType::from(&a), CircuitType::from(&b));
            assert_count!(LessThanOrEqual(Integer<I>, Integer<I>) => Boolean, &case);
            assert_output_type!(LessThanOrEqual(Integer<I>, Integer<I>) => Boolean, case, candidate);
        });
        Circuit::reset();
    }

    fn run_test<I: IntegerType>(mode_a: Mode, mode_b: Mode) {
        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut test_rng());
            let second: I = UniformRand::rand(&mut test_rng());

            let name = format!("LessThanOrEqual: ({}, {}) - {}th iteration", mode_a, mode_b, i);
            check_is_less_than_or_equal(&name, first, second, mode_a, mode_b);
        }
    }

    fn run_exhaustive_test<I: IntegerType>(mode_a: Mode, mode_b: Mode)
    where
        RangeInclusive<I>: Iterator<Item = I>,
    {
        for first in I::MIN..=I::MAX {
            for second in I::MIN..=I::MAX {
                let name = format!("LessThanOrEqual: ({}, {})", first, second);
                check_is_less_than_or_equal(&name, first, second, mode_a, mode_b);
            }
        }
    }

    test_integer_binary!(run_test, i8, is_less_than_or_equal);
    test_integer_binary!(run_test, i16, is_less_than_or_equal);
    test_integer_binary!(run_test, i32, is_less_than_or_equal);
    test_integer_binary!(run_test, i64, is_less_than_or_equal);
    test_integer_binary!(run_test, i128, is_less_than_or_equal);

    test_integer_binary!(run_test, u8, is_less_than_or_equal);
    test_integer_binary!(run_test, u16, is_less_than_or_equal);
    test_integer_binary!(run_test, u32, is_less_than_or_equal);
    test_integer_binary!(run_test, u64, is_less_than_or_equal);
    test_integer_binary!(run_test, u128, is_less_than_or_equal);

    test_integer_binary!(#[ignore], run_exhaustive_test, u8, is_less_than_or_equal, exhaustive);
    test_integer_binary!(#[ignore], run_exhaustive_test, i8, is_less_than_or_equal, exhaustive);
}
