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

impl<E: Environment, I: IntegerType> Not for Integer<E, I> {
    type Output = Integer<E, I>;

    fn not(self) -> Self::Output {
        (&self).not()
    }
}

impl<E: Environment, I: IntegerType> Not for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn not(self) -> Self::Output {
        // Flip each bit in the representation of the `self` integer.
        Integer { bits_le: self.bits_le.iter().map(|b| !b).collect(), phantom: Default::default() }
    }
}

impl<E: Environment, I: IntegerType> Metrics<dyn Not<Output = Integer<E, I>>> for Integer<E, I> {
    type Case = Mode;

    fn count(_case: &Self::Case) -> Count {
        Count::is(0, 0, 0, 0)
    }
}

impl<E: Environment, I: IntegerType> OutputMode<dyn Not<Output = Integer<E, I>>> for Integer<E, I> {
    type Case = Mode;

    fn output_mode(case: &Self::Case) -> Mode {
        match case {
            Mode::Constant => Mode::Constant,
            _ => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    use core::ops::RangeInclusive;

    const ITERATIONS: u64 = 128;

    fn check_not<I: IntegerType + Not<Output = I>>(
        name: &str,
        first: console::Integer<<Circuit as Environment>::Network, I>,
        mode: Mode,
    ) {
        let a = Integer::<Circuit, I>::new(mode, first);
        let expected = !first;

        Circuit::scope(name, || {
            let candidate = a.not();
            assert_eq!(expected, candidate.eject_value());
            assert_count!(Not(Integer<I>) => Integer<I>, &mode);
            assert_output_mode!(Not(Integer<I>) => Integer<I>, &mode, candidate);
        });
        Circuit::reset();
    }

    fn run_test<I: IntegerType + Not<Output = I>>(mode: Mode) {
        for i in 0..ITERATIONS {
            let name = format!("Not: {} {}", mode, i);
            let value = Uniform::rand(&mut test_rng());
            check_not::<I>(&name, value, mode);
        }

        // Check the 0 case.
        let name = format!("Not: {} zero", mode);
        check_not::<I>(&name, console::Integer::zero(), mode);

        // Check the 1 case.
        let name = format!("Not: {} one", mode);
        check_not::<I>(&name, console::Integer::one(), mode);
    }

    fn run_exhaustive_test<I: IntegerType + Not<Output = I>>(mode: Mode)
    where
        RangeInclusive<I>: Iterator<Item = I>,
    {
        for value in I::MIN..=I::MAX {
            let value = console::Integer::<_, I>::new(value);

            let name = format!("Not: {}", mode);
            check_not::<I>(&name, value, mode);
        }
    }

    test_integer_unary!(run_test, i8, not);
    test_integer_unary!(run_test, i16, not);
    test_integer_unary!(run_test, i32, not);
    test_integer_unary!(run_test, i64, not);
    test_integer_unary!(run_test, i128, not);

    test_integer_unary!(run_test, u8, not);
    test_integer_unary!(run_test, u16, not);
    test_integer_unary!(run_test, u32, not);
    test_integer_unary!(run_test, u64, not);
    test_integer_unary!(run_test, u128, not);

    test_integer_unary!(#[ignore], run_exhaustive_test, u8, not, exhaustive);
    test_integer_unary!(#[ignore], run_exhaustive_test, i8, not, exhaustive);
}
