// Copyright 2024 Aleo Network Foundation
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:

// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

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

impl<E: Environment, I: IntegerType> Metrics<dyn Ternary<Boolean = Boolean<E>, Output = Integer<E, I>>>
    for Integer<E, I>
{
    type Case = (Mode, Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        match case {
            (Mode::Constant, _, _)
            | (Mode::Public, Mode::Constant, Mode::Constant)
            | (Mode::Private, Mode::Constant, Mode::Constant) => Count::is(0, 0, 0, 0),
            _ => Count::is(0, 0, I::BITS, I::BITS),
        }
    }
}

impl<E: Environment, I: IntegerType> OutputMode<dyn Ternary<Boolean = Boolean<E>, Output = Integer<E, I>>>
    for Integer<E, I>
{
    type Case = (CircuitType<Boolean<E>>, Mode, Mode);

    fn output_mode(case: &Self::Case) -> Mode {
        let (condition, mode_a, mode_b) = case;
        match condition.mode().is_constant() {
            true => match condition {
                CircuitType::Constant(constant) => match constant.eject_value() {
                    true => *mode_a,
                    false => *mode_b,
                },
                _ => E::halt("The constant condition is required to determine output mode."),
            },
            false => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    fn run_test<I: IntegerType>(mode_condition: Mode, mode_a: Mode, mode_b: Mode) {
        let mut rng = TestRng::default();

        for flag in &[true, false] {
            let first = Uniform::rand(&mut rng);
            let second = Uniform::rand(&mut rng);
            let expected = if *flag { first } else { second };

            let condition = Boolean::<Circuit>::new(mode_condition, *flag);
            let a = Integer::<Circuit, I>::new(mode_a, first);
            let b = Integer::new(mode_b, second);

            let name = format!("Ternary({flag}): if ({mode_condition}) then ({mode_a}) else ({mode_b})");
            Circuit::scope(name, || {
                let candidate = Integer::ternary(&condition, &a, &b);
                assert_eq!(expected, candidate.eject_value());
                assert_count!(Ternary(Boolean, Integer<I>, Integer<I>) => Integer<I>, &(mode_condition, mode_a, mode_b));
                // assert_output_mode!(Ternary(Boolean, Integer<I>, Integer<I>) => Integer<I>, &(CircuitType::from(&condition), mode_a, mode_b), candidate);
            });
            Circuit::reset();
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
}
