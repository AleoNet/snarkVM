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

impl<E: Environment, I: IntegerType, M: Magnitude> PowWrapped<Integer<E, M>> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn pow_wrapped(&self, other: &Integer<E, M>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the result and return the new constant.
            // This cast is safe since Magnitude other can only be `u8`, `u16`, or `u32`.
            witness!(|self, other| self.wrapping_pow(&other.to_u32().unwrap()))
        } else {
            let mut result = Self::one();
            for bit in other.bits_le.iter().rev() {
                result = (&result).mul_wrapped(&result);
                result = Self::ternary(bit, &result.mul_wrapped(self), &result);
            }
            result
        }
    }
}

impl<E: Environment, I: IntegerType, M: Magnitude> Metadata<dyn PowWrapped<Integer<E, M>, Output = Integer<E, I>>>
    for Integer<E, I>
{
    type Case = (CircuitType<Self>, CircuitType<Integer<E, M>>);
    type OutputType = CircuitType<Self>;

    fn count(case: &Self::Case) -> Count {
        // Note that we need to clone `case` so that we can pass it to `output_type!`.
        match case {
            (CircuitType::Constant(_), CircuitType::Constant(_)) => Count::is(I::BITS, 0, 0, 0),
            (type_a, type_b) => {
                let one_count = count!(Integer<E, I>, One<Boolean = Boolean<E>>, &());
                let one_type = output_type!(Integer<E, I>, One<Boolean = Boolean<E>>, ());

                (0..M::BITS)
                    .rev()
                    .fold((one_type, one_count), |(prev_type, prev_count), i| {
                        let case = (prev_type.clone(), prev_type);
                        let square_count = count!(Self, MulWrapped<Self, Output=Self>, &case);
                        let square_type = output_type!(Self, MulWrapped<Self, Output = Self>, case);

                        let case = (square_type.clone(), type_a.clone());
                        let mul_count = count!(Self, MulWrapped<Self, Output=Self>, &case);
                        let mul_type = output_type!(Self, MulWrapped<Self, Output=Self>, case);

                        let bit_type = match type_b.clone() {
                            // This case is safe as M::BITS never exceeds 32.
                            CircuitType::Constant(constant) => {
                                CircuitType::from(&constant.circuit().bits_le[i as usize])
                            }
                            CircuitType::Public => CircuitType::Public,
                            CircuitType::Private => CircuitType::Private,
                        };

                        let case = (bit_type, mul_type, square_type);
                        let result_count = count!(Self, Ternary<Boolean = Boolean<E>, Output = Self>, &case);
                        let result_type = output_type!(Self, Ternary<Boolean = Boolean<E>, Output = Self>, case);

                        (result_type, prev_count + square_count + mul_count + result_count)
                    })
                    .1
            }
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case {
            (CircuitType::Constant(a), CircuitType::Constant(b)) => {
                CircuitType::from(a.circuit().pow_wrapped(&b.circuit()))
            }
            (type_a, type_b) => {
                let one_type = output_type!(Integer<E, I>, One<Boolean = Boolean<E>>, ());

                (0..M::BITS).rev().fold(one_type, |prev_type, i| {
                    let case = (prev_type.clone(), prev_type);
                    let square_type = output_type!(Self, MulWrapped<Self, Output = Self>, case);

                    let case = (square_type.clone(), type_a.clone());
                    let mul_type = output_type!(Self, MulWrapped<Self, Output=Self>, case);

                    let bit_type = match type_b.clone() {
                        // This case is safe as M::BITS never exceeds 32.
                        CircuitType::Constant(constant) => CircuitType::from(&constant.circuit().bits_le[i as usize]),
                        CircuitType::Public => CircuitType::Public,
                        CircuitType::Private => CircuitType::Private,
                    };

                    let case = (bit_type, mul_type, square_type);
                    let result_type = output_type!(Self, Ternary<Boolean = Boolean<E>, Output = Self>, case);

                    result_type
                })
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    use core::{ops::RangeInclusive, panic::RefUnwindSafe};

    // Lowered to 4; we run (~6 * ITERATIONS) cases for most tests.
    const ITERATIONS: u64 = 4;

    fn check_pow<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(
        name: &str,
        first: I,
        second: M,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, M>::new(mode_b, second);
        let case = (CircuitType::from(&a), CircuitType::from(&b));

        let expected = first.wrapping_pow(&second.to_u32().unwrap());

        Circuit::scope(name, || {
            let candidate = a.pow_wrapped(&b);
            println!("{} ^ {} = {}", a.eject_value(), b.eject_value(), candidate.eject_value());
            assert_eq!(expected, candidate.eject_value());
            assert_count!(PowWrapped(Integer<I>, Integer<M>) => Integer<I>, &case);
            assert_output_type!(PowWrapped(Integer<I>, Integer<M>) => Integer<I>, case, candidate);
        });
        Circuit::reset();
    }

    fn run_test<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(mode_a: Mode, mode_b: Mode) {
        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut test_rng());
            let second: M = UniformRand::rand(&mut test_rng());

            let name = format!("Pow: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, second, mode_a, mode_b);

            let name = format!("Pow Zero: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::zero(), mode_a, mode_b);

            let name = format!("Pow One: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::one(), mode_a, mode_b);

            // Check that the square is computed correctly.
            let name = format!("Square: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::one() + M::one(), mode_a, mode_b);

            // Check that the cube is computed correctly.
            let name = format!("Cube: {} ** {} {}", mode_a, mode_b, i);
            check_pow(&name, first, M::one() + M::one() + M::one(), mode_a, mode_b);
        }

        // Test corner cases for exponentiation.
        check_pow("MAX ** MAX", I::MAX, M::MAX, mode_a, mode_b);
        check_pow("MIN ** 0", I::MIN, M::zero(), mode_a, mode_b);
        check_pow("MAX ** 0", I::MAX, M::zero(), mode_a, mode_b);
        check_pow("MIN ** 1", I::MIN, M::one(), mode_a, mode_b);
        check_pow("MAX ** 1", I::MAX, M::one(), mode_a, mode_b);
    }

    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(mode_a: Mode, mode_b: Mode)
    where
        RangeInclusive<I>: Iterator<Item = I>,
        RangeInclusive<M>: Iterator<Item = M>,
    {
        for first in I::MIN..=I::MAX {
            for second in M::MIN..=M::MAX {
                let name = format!("Pow: ({} ** {})", first, second);
                check_pow(&name, first, second, mode_a, mode_b);
            }
        }
    }

    test_integer_binary!(run_test, i8, u8, pow);
    test_integer_binary!(run_test, i8, u16, pow);
    test_integer_binary!(run_test, i8, u32, pow);

    test_integer_binary!(run_test, i16, u8, pow);
    test_integer_binary!(run_test, i16, u16, pow);
    test_integer_binary!(run_test, i16, u32, pow);

    test_integer_binary!(run_test, i32, u8, pow);
    test_integer_binary!(run_test, i32, u16, pow);
    test_integer_binary!(run_test, i32, u32, pow);

    test_integer_binary!(run_test, i64, u8, pow);
    test_integer_binary!(run_test, i64, u16, pow);
    test_integer_binary!(run_test, i64, u32, pow);

    test_integer_binary!(run_test, i128, u8, pow);
    test_integer_binary!(run_test, i128, u16, pow);
    test_integer_binary!(run_test, i128, u32, pow);

    test_integer_binary!(run_test, u8, u8, pow);
    test_integer_binary!(run_test, u8, u16, pow);
    test_integer_binary!(run_test, u8, u32, pow);

    test_integer_binary!(run_test, u16, u8, pow);
    test_integer_binary!(run_test, u16, u16, pow);
    test_integer_binary!(run_test, u16, u32, pow);

    test_integer_binary!(run_test, u32, u8, pow);
    test_integer_binary!(run_test, u32, u16, pow);
    test_integer_binary!(run_test, u32, u32, pow);

    test_integer_binary!(run_test, u64, u8, pow);
    test_integer_binary!(run_test, u64, u16, pow);
    test_integer_binary!(run_test, u64, u32, pow);

    test_integer_binary!(run_test, u128, u8, pow);
    test_integer_binary!(run_test, u128, u16, pow);
    test_integer_binary!(run_test, u128, u32, pow);

    test_integer_binary!(#[ignore], run_exhaustive_test, u8, u8, pow, exhaustive);
    test_integer_binary!(#[ignore], run_exhaustive_test, i8, u8, pow, exhaustive);
}
