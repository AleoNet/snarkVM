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

impl<E: Environment, I: IntegerType> AbsWrapped for Integer<E, I> {
    type Output = Integer<E, I>;

    fn abs_wrapped(self) -> Self::Output {
        (&self).abs_wrapped()
    }
}

impl<E: Environment, I: IntegerType> AbsWrapped for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn abs_wrapped(self) -> Self::Output {
        match I::is_signed() {
            true => Integer::ternary(self.msb(), &Integer::zero().sub_wrapped(self), self),
            false => self.clone(),
        }
    }
}

impl<E: Environment, I: IntegerType> Metrics<dyn AbsWrapped<Output = Integer<E, I>>> for Integer<E, I> {
    type Case = Mode;

    fn count(case: &Self::Case) -> Count {
        match I::is_signed() {
            true => match case {
                Mode::Constant => Count::is(2 * I::BITS, 0, 0, 0),
                _ => Count::is(I::BITS, 0, (2 * I::BITS) + 1, (2 * I::BITS) + 2),
            },
            false => Count::is(0, 0, 0, 0),
        }
    }
}

impl<E: Environment, I: IntegerType> OutputMode<dyn AbsWrapped<Output = Integer<E, I>>> for Integer<E, I> {
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

    use core::{ops::RangeInclusive, panic::UnwindSafe};

    const ITERATIONS: u64 = 128;

    fn check_abs<I: IntegerType + UnwindSafe>(name: &str, value: I, mode: Mode) {
        let a = Integer::<Circuit, I>::new(mode, value);
        let expected = value.wrapping_abs();
        Circuit::scope(name, || {
            let candidate = a.abs_wrapped();
            assert_eq!(expected, candidate.eject_value());
            assert_count!(AbsWrapped(Integer<I>) => Integer<I>, &mode);
            assert_output_mode!(AbsWrapped(Integer<I>) => Integer<I>, &mode, candidate);
        });
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

        // Check the I::MIN (wrapped) case.
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
