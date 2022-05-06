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

impl<E: Environment, I: IntegerType> Add<Integer<E, I>> for Integer<E, I> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        self + &other
    }
}

impl<E: Environment, I: IntegerType> Add<Integer<E, I>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn add(self, other: Integer<E, I>) -> Self::Output {
        self + &other
    }
}

impl<E: Environment, I: IntegerType> Add<&Integer<E, I>> for Integer<E, I> {
    type Output = Self;

    fn add(self, other: &Self) -> Self::Output {
        &self + other
    }
}

impl<E: Environment, I: IntegerType> Add<&Integer<E, I>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn add(self, other: &Integer<E, I>) -> Self::Output {
        let mut output = self.clone();
        output += other;
        output
    }
}

impl<E: Environment, I: IntegerType> AddAssign<Integer<E, I>> for Integer<E, I> {
    fn add_assign(&mut self, other: Integer<E, I>) {
        *self += &other;
    }
}

impl<E: Environment, I: IntegerType> AddAssign<&Integer<E, I>> for Integer<E, I> {
    fn add_assign(&mut self, other: &Integer<E, I>) {
        // Stores the sum of `self` and `other` in `self`.
        *self = self.add_checked(other);
    }
}

impl<E: Environment, I: IntegerType> AddChecked<Self> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn add_checked(&self, other: &Integer<E, I>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the sum and return the new constant.
            match self.eject_value().checked_add(&other.eject_value()) {
                Some(value) => Integer::constant(value),
                None => E::halt("Integer overflow on addition of two constants"),
            }
        } else {
            // Instead of adding the bits of `self` and `other` directly, the integers are
            // converted into a field elements, and summed, before converting back to integers.
            // Note: This is safe as the field is larger than the maximum integer type supported.
            let sum = self.to_field() + other.to_field();

            // Extract the integer bits from the field element, with a carry bit.
            let (sum, carry) = match sum.to_lower_bits_le(I::BITS as usize + 1).split_last() {
                Some((carry, bits_le)) => (Integer::from_bits_le(bits_le), carry.clone()),
                None => E::halt("Malformed sum detected during integer addition"),
            };

            // Check for overflow.
            match I::is_signed() {
                // For signed addition, overflow and underflow conditions are:
                //   - a > 0 && b > 0 && a + b < 0 (Overflow)
                //   - a < 0 && b < 0 && a + b > 0 (Underflow)
                //   - Note: if sign(a) != sign(b) then over/underflow is impossible.
                //   - Note: the result of an overflow and underflow must be negative and positive, respectively.
                true => {
                    let is_same_sign = self.msb().is_equal(other.msb());
                    let is_overflow = is_same_sign & sum.msb().is_not_equal(self.msb());
                    E::assert_eq(is_overflow, E::zero());
                }
                // For unsigned addition, ensure the carry bit is zero.
                false => E::assert_eq(carry, E::zero()),
            }

            // Return the sum of `self` and `other`.
            sum
        }
    }
}

impl<E: Environment, I: IntegerType> Metadata<dyn Add<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (CircuitType<Self>, CircuitType<Self>);
    type OutputType = CircuitType<Self>;

    fn count(case: &Self::Case) -> Count {
        count!(Self, AddChecked<Self, Output = Self>, case)
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        output_type!(Self, AddChecked<Self, Output = Self>, case)
    }
}

impl<E: Environment, I: IntegerType> Metadata<dyn AddChecked<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (CircuitType<Self>, CircuitType<Self>);
    type OutputType = CircuitType<Self>;

    fn count(case: &Self::Case) -> Count {
        match I::is_signed() {
            true => match (case.0.eject_mode(), case.1.eject_mode()) {
                (Mode::Constant, Mode::Constant) => Count::is(I::BITS, 0, 0, 0),
                (Mode::Constant, _) => Count::is(0, 0, I::BITS + 2, I::BITS + 4),
                (_, Mode::Constant) => Count::is(0, 0, I::BITS + 3, I::BITS + 5),
                (_, _) => Count::is(0, 0, I::BITS + 4, I::BITS + 6),
            },
            false => match (case.0.eject_mode(), case.1.eject_mode()) {
                (Mode::Constant, Mode::Constant) => Count::is(I::BITS, 0, 0, 0),
                (_, _) => Count::is(0, 0, I::BITS + 1, I::BITS + 3),
            },
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match (case.0.eject_mode(), case.1.eject_mode()) {
            (Mode::Constant, Mode::Constant) => CircuitType::from(case.0.circuit().add_checked(case.1.circuit())),
            (_, _) => CircuitType::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_integer_binary;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};
    use test_utilities::*;

    use core::{ops::RangeInclusive, panic::RefUnwindSafe};

    const ITERATIONS: u64 = 128;

    fn check_add<I: IntegerType + RefUnwindSafe>(name: &str, first: I, second: I, mode_a: Mode, mode_b: Mode) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::new(mode_b, second);
        match first.checked_add(&second) {
            Some(expected) => Circuit::scope(name, || {
                let candidate = a.add_checked(&b);
                assert_eq!(expected, candidate.eject_value());

                let case = (CircuitType::from(a), CircuitType::from(b));
                assert_count!(Add(Integer<I>, Integer<I>) => Integer<I>, &case);
                assert_output_type!(Add(Integer<I>, Integer<I>) => Integer<I>, case, candidate);
            }),
            None => match mode_a.is_constant() && mode_b.is_constant() {
                true => check_operation_halts(&a, &b, Integer::add_checked),
                false => Circuit::scope(name, || {
                    let _candidate = a.add_checked(&b);

                    let case = (CircuitType::from(a), CircuitType::from(b));
                    assert_count_fails!(Add(Integer<I>, Integer<I>) => Integer<I>, &case);
                }),
            },
        }
        Circuit::reset();
    }

    fn run_test<I: IntegerType + RefUnwindSafe>(mode_a: Mode, mode_b: Mode) {
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

    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe>(mode_a: Mode, mode_b: Mode)
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
