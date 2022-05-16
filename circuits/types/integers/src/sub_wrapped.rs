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

impl<E: Environment, I: IntegerType> SubWrapped<Self> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn sub_wrapped(&self, other: &Integer<E, I>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the difference and return the new constant.
            Integer::new(Mode::Constant, self.eject_value().wrapping_sub(&other.eject_value()))
        } else {
            // Instead of subtracting the bits of `self` and `other` directly, the integers are
            // converted into field elements to perform the operation, before converting back to integers.
            // Note: This is safe as the field is larger than the maximum integer type supported.
            let difference = self.to_field() + (!other).to_field() + Field::one();

            // Extract the integer bits from the field element, with a carry bit.
            let mut bits_le = difference.to_lower_bits_le(I::BITS as usize + 1);
            // Drop the carry bit as the operation is wrapped subtraction.
            bits_le.pop();

            // Return the difference of `self` and `other`.
            Integer { bits_le, phantom: Default::default() }
        }
    }
}

impl<E: Environment, I: IntegerType> Metadata<dyn SubWrapped<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (CircuitType<Self>, CircuitType<Self>);
    type OutputType = CircuitType<Self>;

    fn count(case: &Self::Case) -> Count {
        match case {
            (CircuitType::Constant(_), CircuitType::Constant(_)) => Count::is(I::BITS, 0, 0, 0),
            (_, _) => Count::is(0, 0, I::BITS + 1, I::BITS + 2),
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case {
            (CircuitType::Constant(a), CircuitType::Constant(b)) => {
                CircuitType::from(a.circuit().sub_wrapped(&b.circuit()))
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

    const ITERATIONS: u64 = 128;

    fn check_sub<I: IntegerType>(name: &str, first: I, second: I, mode_a: Mode, mode_b: Mode) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::new(mode_b, second);
        let expected = first.wrapping_sub(&second);
        Circuit::scope(name, || {
            let candidate = a.sub_wrapped(&b);
            assert_eq!(expected, candidate.eject_value());

            let case = (CircuitType::from(a), CircuitType::from(b));
            assert_count!(SubWrapped(Integer<I>, Integer<I>) => Integer<I>, &case);
            assert_output_type!(SubWrapped(Integer<I>, Integer<I>) => Integer<I>, case, candidate);
        });
        Circuit::reset();
    }

    fn run_test<I: IntegerType>(mode_a: Mode, mode_b: Mode) {
        for i in 0..ITERATIONS {
            let name = format!("Sub: {} - {} {}", mode_a, mode_b, i);
            let first: I = UniformRand::rand(&mut test_rng());
            let second: I = UniformRand::rand(&mut test_rng());
            check_sub(&name, first, second, mode_a, mode_b);
        }

        // Overflow
        if I::is_signed() {
            check_sub("MAX - (-1)", I::MAX, I::zero() - I::one(), mode_a, mode_b);
        }
        // Underflow
        check_sub("MIN - 1", I::MIN, I::one(), mode_a, mode_b);
    }

    fn run_exhaustive_test<I: IntegerType>(mode_a: Mode, mode_b: Mode)
    where
        RangeInclusive<I>: Iterator<Item = I>,
    {
        for first in I::MIN..=I::MAX {
            for second in I::MIN..=I::MAX {
                let name = format!("Sub: ({} - {})", first, second);
                check_sub(&name, first, second, mode_a, mode_b);
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
