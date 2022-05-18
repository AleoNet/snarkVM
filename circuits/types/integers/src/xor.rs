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

impl<E: Environment, I: IntegerType> BitXor<Integer<E, I>> for Integer<E, I> {
    type Output = Self;

    /// Returns `(self != other)`.
    fn bitxor(self, other: Self) -> Self::Output {
        self ^ &other
    }
}

impl<E: Environment, I: IntegerType> BitXor<Integer<E, I>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    /// Returns `(self != other)`.
    fn bitxor(self, other: Integer<E, I>) -> Self::Output {
        self ^ &other
    }
}

impl<E: Environment, I: IntegerType> BitXor<&Integer<E, I>> for Integer<E, I> {
    type Output = Self;

    /// Returns `(self != other)`.
    fn bitxor(self, other: &Self) -> Self::Output {
        &self ^ other
    }
}

impl<E: Environment, I: IntegerType> BitXor<&Integer<E, I>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    /// Returns `(self != other)`.
    fn bitxor(self, other: &Integer<E, I>) -> Self::Output {
        let mut output = self.clone();
        output ^= other;
        output
    }
}

impl<E: Environment, I: IntegerType> BitXorAssign<Integer<E, I>> for Integer<E, I> {
    /// Sets `self` as `(self != other)`.
    fn bitxor_assign(&mut self, other: Integer<E, I>) {
        *self ^= &other;
    }
}

impl<E: Environment, I: IntegerType> BitXorAssign<&Integer<E, I>> for Integer<E, I> {
    /// Sets `self` as `(self != other)`.
    fn bitxor_assign(&mut self, other: &Integer<E, I>) {
        // Stores the bitwise XOR of `self` and `other` in `self`.
        *self = Self {
            bits_le: self.bits_le.iter().zip_eq(other.bits_le.iter()).map(|(a, b)| a ^ b).collect(),
            phantom: Default::default(),
        }
    }
}

impl<E: Environment, I: IntegerType> Metadata<dyn BitXor<Integer<E, I>, Output = Integer<E, I>>> for Integer<E, I> {
    type Case = (IntegerCircuitType<E, I>, IntegerCircuitType<E, I>);
    type OutputType = IntegerCircuitType<E, I>;

    fn count(case: &Self::Case) -> Count {
        match case.0.is_constant() || case.1.is_constant() {
            true => Count::is(0, 0, 0, 0),
            false => Count::is(0, 0, I::BITS, I::BITS),
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        let (lhs, rhs) = case;
        IntegerCircuitType {
            bits_le: lhs
                .bits_le
                .into_iter()
                .zip_eq(rhs.bits_le.into_iter())
                .map(|(a, b)| output_type!(Boolean<E>, BitXor<Boolean<E>, Output = Boolean<E>>, (a, b)))
                .collect(),
            phantom: Default::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    use core::ops::RangeInclusive;

    const ITERATIONS: u64 = 128;

    fn check_bitxor<I: IntegerType + BitXor<Output = I>>(name: &str, first: I, second: I, mode_a: Mode, mode_b: Mode) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);
        let expected = first ^ second;
        Circuit::scope(name, || {
            let candidate = (&a).bitxor(&b);
            assert_eq!(expected, candidate.eject_value());

            let case = (IntegerCircuitType::from(a), IntegerCircuitType::from(b));
            assert_count!(BitXor(Integer<I>, Integer<I>) => Integer<I>, &case);
            assert_output_type!(BitXor(Integer<I>, Integer<I>) => Integer<I>, case, candidate);
        });
        Circuit::reset();
    }

    fn run_test<I: IntegerType + BitXor<Output = I>>(mode_a: Mode, mode_b: Mode) {
        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut test_rng());
            let second: I = UniformRand::rand(&mut test_rng());

            let name = format!("BitXor: ({} ^ {}) {}", mode_a, mode_b, i);
            check_bitxor(&name, first, second, mode_a, mode_b);
            check_bitxor(&name, second, first, mode_a, mode_b); // Commute the operation.

            let name = format!("BitXor Identity: ({} ^ {}) {}", mode_a, mode_b, i);
            check_bitxor(&name, I::zero(), first, mode_a, mode_b);
            check_bitxor(&name, first, I::zero(), mode_a, mode_b); // Commute the operation.

            let name = format!("BitXor Inverse Identity: ({} ^ {}) {}", mode_a, mode_b, i);
            let inverse = if I::is_signed() { I::zero() - I::one() } else { I::MAX };
            check_bitxor(&name, inverse, first, mode_a, mode_b);
            check_bitxor(&name, first, inverse, mode_a, mode_b); // Commute the operation.
        }

        // Check cases common to signed and unsigned integers.
        check_bitxor("0 ^ MAX", I::zero(), I::MAX, mode_a, mode_b);
        check_bitxor("MAX ^ 0", I::MAX, I::zero(), mode_a, mode_b);
        check_bitxor("0 ^ MIN", I::zero(), I::MIN, mode_a, mode_b);
        check_bitxor("MIN ^ 0", I::MIN, I::zero(), mode_a, mode_b);
    }

    fn run_exhaustive_test<I: IntegerType + BitXor<Output = I>>(mode_a: Mode, mode_b: Mode)
    where
        RangeInclusive<I>: Iterator<Item = I>,
    {
        for first in I::MIN..=I::MAX {
            for second in I::MIN..=I::MAX {
                let name = format!("BitXor: ({} ^ {})", first, second);
                check_bitxor(&name, first, second, mode_a, mode_b);
            }
        }
    }

    test_integer_binary!(run_test, i8, bitxor);
    test_integer_binary!(run_test, i16, bitxor);
    test_integer_binary!(run_test, i32, bitxor);
    test_integer_binary!(run_test, i64, bitxor);
    test_integer_binary!(run_test, i128, bitxor);

    test_integer_binary!(run_test, u8, bitxor);
    test_integer_binary!(run_test, u16, bitxor);
    test_integer_binary!(run_test, u32, bitxor);
    test_integer_binary!(run_test, u64, bitxor);
    test_integer_binary!(run_test, u128, bitxor);

    test_integer_binary!(#[ignore], run_exhaustive_test, u8, bitxor, exhaustive);
    test_integer_binary!(#[ignore], run_exhaustive_test, i8, bitxor, exhaustive);
}
