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

impl<E: Environment, I: IntegerType> Ternary for Integer<E, I> {
    type Boolean = Boolean<E>;
    type Output = Self;

    /// Returns `first` if `condition` is `true`, otherwise returns `second`.
    fn ternary(condition: &Self::Boolean, first: &Self, second: &Self) -> Self::Output {
        // Constant `condition`
        if condition.is_constant() {
            match condition.eject_value() {
                true => first.clone(),
                false => second.clone(),
            }
        }
        // Variables
        else {
            // Directly instantiate the integer, rather than invoking `from_bits_le`
            // since the modes of each individual bit varies depending on the modes
            // and values of `condition`, `first_bit`, and `second_bit`.
            Self {
                bits_le: first
                    .bits_le
                    .iter()
                    .zip_eq(second.bits_le.iter())
                    .map(|(first_bit, second_bit)| Self::Boolean::ternary(condition, first_bit, second_bit))
                    .collect(),
                phantom: Default::default(),
            }
        }
    }
}

impl<E: Environment, I: IntegerType> Metadata<dyn Ternary<Boolean = Boolean<E>, Output = Integer<E, I>>>
    for Integer<E, I>
{
    type Case = (CircuitType<Boolean<E>>, CircuitType<Self>, CircuitType<Self>);
    type OutputType = CircuitType<Self>;

    fn count(case: &Self::Case) -> Count {
        match case {
            (CircuitType::Constant(_), _, _)
            | (CircuitType::Public, CircuitType::Constant(_), CircuitType::Constant(_))
            | (CircuitType::Private, CircuitType::Constant(_), CircuitType::Constant(_)) => Count::is(0, 0, 0, 0),
            _ => Count::is(0, 0, I::BITS, I::BITS),
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case {
            (CircuitType::Constant(constant), first_type, second_type) => match constant.eject_value() {
                true => first_type,
                false => second_type,
            },
            (condition_type, CircuitType::Constant(a), CircuitType::Constant(b)) => {
                let output_bit_types = a
                    .circuit()
                    .bits_le
                    .into_iter()
                    .zip_eq(b.circuit().bits_le.into_iter())
                    .map(|(self_bit, other_bit)| {
                        let case = (condition_type.clone(), CircuitType::from(self_bit), CircuitType::from(other_bit));
                        output_type!(Boolean<E>, Ternary<Boolean = Boolean<E>, Output = Boolean<E>>, case)
                    })
                    .collect::<Vec<_>>();

                let mut output_bits = Vec::with_capacity(output_bit_types.len());
                let mut output_mode = Mode::Constant;
                for bit_type in output_bit_types {
                    match bit_type {
                        CircuitType::Constant(bit) => output_bits.push(bit.circuit()),
                        CircuitType::Public => {
                            output_mode = if output_mode != Mode::Private { Mode::Public } else { output_mode }
                        }
                        CircuitType::Private => output_mode = Mode::Private,
                    }
                }
                match output_mode {
                    Mode::Constant => CircuitType::from(Self { bits_le: output_bits, phantom: Default::default() }),
                    Mode::Public => CircuitType::Public,
                    Mode::Private => CircuitType::Private,
                }
            }
            _ => CircuitType::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};
    use std::{ops::RangeInclusive, panic::RefUnwindSafe};

    fn check_ternary<I: IntegerType>(
        name: &str,
        flag: &bool,
        first: I,
        second: I,
        mode_condition: Mode,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);
        let condition = Boolean::<Circuit>::new(mode_condition, *flag);

        let expected = if *flag { first } else { second };

        Circuit::scope(name, || {
            let candidate = Integer::ternary(&condition, &a, &b);
            assert_eq!(expected, candidate.eject_value());

            println!("Ternary: if {:?} then {:?} else {:?}", condition.eject_value(), a.eject_value(), b.eject_value());
            let case = (CircuitType::from(condition), CircuitType::from(a), CircuitType::from(b));
            assert_count!(Ternary(Boolean, Integer<I>, Integer<I>) => Integer<I>, &case);
            assert_output_type!(Ternary(Boolean, Integer<I>, Integer<I>) => Integer<I>, case, candidate);
        });
        Circuit::reset();
    }

    fn run_test<I: IntegerType>(mode_condition: Mode, mode_a: Mode, mode_b: Mode) {
        for flag in &[true, false] {
            let first: I = UniformRand::rand(&mut test_rng());
            let second: I = UniformRand::rand(&mut test_rng());

            let name = format!("Ternary({}): if ({}) then ({}) else ({})", flag, mode_condition, mode_a, mode_b);
            check_ternary(&name, flag, first, second, mode_condition, mode_a, mode_b);
        }
    }

    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe>(mode_condition: Mode, mode_a: Mode, mode_b: Mode)
    where
        RangeInclusive<I>: Iterator<Item = I>,
    {
        for flag in &[true, false] {
            for first in I::MIN..=I::MAX {
                for second in I::MIN..=I::MAX {
                    let name =
                        format!("Ternary({}): if ({}) then ({}) else ({})", flag, mode_condition, mode_a, mode_b);
                    check_ternary(&name, flag, first, second, mode_condition, mode_a, mode_b);
                }
            }
        }
    }

    test_integer_ternary!(run_test, i8, if, then, else);
    test_integer_ternary!(run_test, i16, if, then, else);
    test_integer_ternary!(run_test, i32, if, then, else);
    test_integer_ternary!(run_test, i64, if, then, else);
    test_integer_ternary!(run_test, i128, if, then, else);

    test_integer_ternary!(run_test, u8, if, then, else);
    test_integer_ternary!(run_test, u16, if, then, else);
    test_integer_ternary!(run_test, u32, if, then, else);
    test_integer_ternary!(run_test, u64, if, then, else);
    test_integer_ternary!(run_test, u128, if, then, else);

    test_integer_ternary!(#[ignore], run_exhaustive_test, u8, if, then, else, exhaustive);
    test_integer_ternary!(#[ignore], run_exhaustive_test, i8, if, then, else, exhaustive);
}
