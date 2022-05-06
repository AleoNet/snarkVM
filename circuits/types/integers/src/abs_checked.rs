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

impl<E: Environment, I: IntegerType> Metadata<dyn AbsChecked<Output = Integer<E, I>>> for Integer<E, I> {
    type Case = CircuitType<Integer<E, I>>;
    type OutputType = CircuitType<Integer<E, I>>;

    fn count(case: &Self::Case) -> Count {
        match I::is_signed() {
            true => match case.eject_mode() {
                Mode::Constant => Count::is(2 * I::BITS, 0, 0, 0),
                _ => Count::is(I::BITS, 0, (2 * I::BITS) + 3, (2 * I::BITS) + 5),
            },
            false => Count::is(0, 0, 0, 0),
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match I::is_signed() {
            true => match case.is_constant() {
                true => CircuitType::from(case.circuit().abs_checked()),
                false => CircuitType::Private,
            },
            false => case,
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

    const ITERATIONS: u64 = 128;

    fn check_abs<I: IntegerType + UnwindSafe>(name: &str, value: I, mode: Mode) {
        let a = Integer::<Circuit, I>::new(mode, value);
        match value.checked_abs() {
            Some(expected) => Circuit::scope(name, || {
                let candidate = (&a).abs_checked();
                assert_eq!(expected, candidate.eject_value());

                let case = CircuitType::from(a);
                assert_count!(AbsChecked(Integer<I>) => Integer<I>, &case);
                assert_output_type!(AbsChecked(Integer<I>) => Integer<I>, case, candidate);
            }),
            None => match mode {
                Mode::Constant => check_unary_operation_halts(a, |a: Integer<Circuit, I>| a.abs_checked()),
                _ => Circuit::scope(name, || {
                    let _candidate = (&a).abs_checked();

                    let case = CircuitType::from(a);
                    assert_count_fails!(AbsChecked(Integer<I>) => Integer<I>, &case);
                }),
            },
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
            let name = format!("Abs: {}", mode);
            check_abs(&name, value, mode);
        }
    }

    test_integer_unary!(run_test, i8, abs_checked);
    test_integer_unary!(run_test, i16, abs_checked);
    test_integer_unary!(run_test, i32, abs_checked);
    test_integer_unary!(run_test, i64, abs_checked);
    test_integer_unary!(run_test, i128, abs_checked);

    test_integer_unary!(run_test, u8, abs_checked);
    test_integer_unary!(run_test, u16, abs_checked);
    test_integer_unary!(run_test, u32, abs_checked);
    test_integer_unary!(run_test, u64, abs_checked);
    test_integer_unary!(run_test, u128, abs_checked);

    test_integer_unary!(#[ignore], run_exhaustive_test, u8, abs_checked, exhaustive);
    test_integer_unary!(#[ignore], run_exhaustive_test, i8, abs_checked, exhaustive);
}
