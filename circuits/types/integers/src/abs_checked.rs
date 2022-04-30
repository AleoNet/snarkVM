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

impl<E: Environment, I: IntegerType> AbsChecked for Integer<E, I> {
    type Output = Integer<E, I>;

    fn abs_checked(self) -> Self::Output {
        (&self).abs_checked()
    }
}

impl<E: Environment, I: IntegerType> AbsChecked for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn abs_checked(self) -> Self::Output {
        match I::is_signed() {
            true => Integer::ternary(self.msb(), &Integer::zero().sub_checked(self), self),
            false => self.clone(),
        }
    }
}

impl<E: Environment, I: IntegerType> Metrics<dyn AbsChecked<Output = Integer<E, I>>> for Integer<E, I> {
    type Case = Mode;

    fn count(case: &Self::Case) -> Count {
        match I::is_signed() {
            true => match case {
                Mode::Constant => Count::is(2 * I::BITS, 0, 0, 0),
                _ => Count::is(I::BITS, 0, (2 * I::BITS) + 3, (2 * I::BITS) + 5),
            },
            false => Count::is(0, 0, 0, 0),
        }
    }
}

impl<E: Environment, I: IntegerType> OutputMode<dyn AbsChecked<Output = Integer<E, I>>> for Integer<E, I> {
    type Case = Mode;

    fn output_mode(case: &Self::Case) -> Mode {
        match I::is_signed() {
            true => match case.is_constant() {
                true => Mode::Constant,
                false => Mode::Private,
            },
            false => *case,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};
    use test_utilities::*;

    use core::{ops::RangeInclusive, panic::UnwindSafe};

    const ITERATIONS: usize = 128;

    #[rustfmt::skip]
    fn check_abs<I: IntegerType + UnwindSafe>(
        name: &str,
        value: I,
        mode: Mode
    ) {
        let a = Integer::<Circuit, I>::new(mode, value);
        match value.checked_abs() {
            Some(expected) => Circuit::scope(name, || {
                let candidate = a.abs_checked();
                assert_eq!(expected, candidate.eject_value());
                assert_count!(Integer<Circuit, I>, AbsChecked<Output = Integer<Circuit, I>>, &mode);
                assert_output_mode!(candidate, Integer<Circuit, I>, AbsChecked<Output = Integer<Circuit, I>>, &mode);
            }),
            None => match mode {
                Mode::Constant => check_unary_operation_halts(a, |a: Integer<Circuit, I>| a.abs_checked()),
                _ => Circuit::scope(name, || {
                    let _candidate = a.abs_checked();
                    assert_count_fails!(Integer<Circuit, I>, AbsChecked<Output = Integer<Circuit, I>>, &mode);
                })
            }
        }
        Circuit::reset();
    }

    fn run_test<I: IntegerType + UnwindSafe>(mode: Mode) {
        for i in 0..ITERATIONS {
            let name = format!("Abs: {} {}", mode, i);
            let value: I = UniformRand::rand(&mut test_rng());
            check_abs(&name, value, mode);
        }

        // Check the 0 case.
        let name = format!("Abs: {} zero", mode);
        check_abs(&name, I::zero(), mode);

        // Check the 1 case.
        let name = format!("Abs: {} one", mode);
        check_abs(&name, I::one(), mode);

        // Check the I::MIN (checked) case.
        let name = format!("Abs: {} one", mode);
        check_abs(&name, I::MIN, mode);
    }

    fn run_exhaustive_test<I: IntegerType + UnwindSafe>(mode: Mode)
    where
        RangeInclusive<I>: Iterator<Item = I>,
    {
        for value in I::MIN..=I::MAX {
            check_abs(&format!("Abs: {}", mode), value, mode);
        }
    }

    test_integer_unary!(run_test, i8, equals);
    test_integer_unary!(run_test, i16, equals);
    test_integer_unary!(run_test, i32, equals);
    test_integer_unary!(run_test, i64, equals);
    test_integer_unary!(run_test, i128, equals);

    test_integer_unary!(run_test, u8, equals);
    test_integer_unary!(run_test, u16, equals);
    test_integer_unary!(run_test, u32, equals);
    test_integer_unary!(run_test, u64, equals);
    test_integer_unary!(run_test, u128, equals);

    test_integer_unary!(#[ignore], run_exhaustive_test, u8, equals, exhaustive);
    test_integer_unary!(#[ignore], run_exhaustive_test, i8, equals, exhaustive);
}
