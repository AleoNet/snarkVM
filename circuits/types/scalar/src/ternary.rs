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

impl<E: Environment> Ternary for Scalar<E> {
    type Boolean = Boolean<E>;
    type Output = Self;

    /// Returns `first` if `condition` is `true`, otherwise returns `second`.
    fn ternary(condition: &Self::Boolean, first: &Self, second: &Self) -> Self::Output {
        let mut bits_le = Vec::with_capacity(first.bits_le.len());

        for (a, b) in first.bits_le.iter().zip_eq(second.bits_le.iter()) {
            bits_le.push(Ternary::ternary(condition, a, b));
        }

        Self { bits_le }
    }
}

impl<E: Environment> Metadata<dyn Ternary<Boolean = Boolean<E>, Output = Scalar<E>>> for Scalar<E> {
    type Case = (CircuitType<Boolean<E>>, CircuitType<Self>, CircuitType<Self>);
    type OutputType = CircuitType<Self>;

    fn count(case: &Self::Case) -> Count {
        match case {
            (CircuitType::Constant(_), _, _) | (_, CircuitType::Constant(_), CircuitType::Constant(_)) => {
                Count::is(0, 0, 0, 0)
            }
            _ => Count::is(0, 0, 251, 251),
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
                    Mode::Constant => CircuitType::from(Self { bits_le: output_bits }),
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

    const ITERATIONS: u64 = 32;

    fn check_ternary(
        name: &str,
        flag: bool,
        first: <Circuit as Environment>::ScalarField,
        second: <Circuit as Environment>::ScalarField,
        mode_condition: Mode,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let expected = if flag { first } else { second };
        let condition = Boolean::<Circuit>::new(mode_condition, flag);
        let a = Scalar::<Circuit>::new(mode_a, first);
        let b = Scalar::<Circuit>::new(mode_b, second);

        Circuit::scope(name, || {
            let case = format!("({} ? {} : {})", condition.eject_value(), a.eject_value(), b.eject_value());
            let candidate = Scalar::ternary(&condition, &a, &b);
            assert_eq!(expected, candidate.eject_value(), "{case}");

            let case = (CircuitType::from(condition), CircuitType::from(a), CircuitType::from(b));
            assert_count!(Ternary(Boolean, Scalar, Scalar) => Scalar, &case);
            assert_output_type!(Ternary(Boolean, Scalar, Scalar) => Scalar, case, candidate);
        });
    }

    fn run_test(mode_condition: Mode, mode_a: Mode, mode_b: Mode) {
        for i in 0..ITERATIONS {
            for flag in [true, false] {
                let name = format!("{} ? {} : {}, {}", flag, mode_a, mode_b, i);
                let check_ternary =
                    |first, second| check_ternary(&name, flag, first, second, mode_condition, mode_a, mode_b);

                let first: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut test_rng());
                let second: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut test_rng());

                check_ternary(first, second);

                // Test corner cases.
                check_ternary(
                    <Circuit as Environment>::ScalarField::zero(),
                    <Circuit as Environment>::ScalarField::zero(),
                );
                check_ternary(
                    <Circuit as Environment>::ScalarField::zero(),
                    <Circuit as Environment>::ScalarField::one(),
                );
                check_ternary(
                    <Circuit as Environment>::ScalarField::one(),
                    <Circuit as Environment>::ScalarField::zero(),
                );
                check_ternary(
                    <Circuit as Environment>::ScalarField::one(),
                    <Circuit as Environment>::ScalarField::one(),
                );
            }
        }
    }

    #[test]
    fn test_if_constant_then_constant_else_constant() {
        run_test(Mode::Constant, Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_if_constant_then_constant_else_public() {
        run_test(Mode::Constant, Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_if_constant_then_constant_else_private() {
        run_test(Mode::Constant, Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_if_constant_then_public_else_constant() {
        run_test(Mode::Constant, Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_if_constant_then_public_else_public() {
        run_test(Mode::Constant, Mode::Public, Mode::Public);
    }

    #[test]
    fn test_if_constant_then_public_else_private() {
        run_test(Mode::Constant, Mode::Public, Mode::Private);
    }

    #[test]
    fn test_if_constant_then_private_else_constant() {
        run_test(Mode::Constant, Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_if_constant_then_private_else_public() {
        run_test(Mode::Constant, Mode::Private, Mode::Public);
    }

    #[test]
    fn test_if_constant_then_private_else_private() {
        run_test(Mode::Constant, Mode::Private, Mode::Private);
    }

    #[test]
    fn test_if_public_then_constant_else_constant() {
        run_test(Mode::Public, Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_if_public_then_constant_else_public() {
        run_test(Mode::Public, Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_if_public_then_constant_else_private() {
        run_test(Mode::Public, Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_if_public_then_public_else_constant() {
        run_test(Mode::Public, Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_if_public_then_public_else_public() {
        run_test(Mode::Public, Mode::Public, Mode::Public);
    }

    #[test]
    fn test_if_public_then_public_else_private() {
        run_test(Mode::Public, Mode::Public, Mode::Private);
    }

    #[test]
    fn test_if_public_then_private_else_constant() {
        run_test(Mode::Public, Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_if_public_then_private_else_public() {
        run_test(Mode::Public, Mode::Private, Mode::Public);
    }

    #[test]
    fn test_if_public_then_private_else_private() {
        run_test(Mode::Public, Mode::Private, Mode::Private);
    }

    #[test]
    fn test_if_private_then_constant_else_constant() {
        run_test(Mode::Private, Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_if_private_then_constant_else_public() {
        run_test(Mode::Private, Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_if_private_then_constant_else_private() {
        run_test(Mode::Private, Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_if_private_then_public_else_constant() {
        run_test(Mode::Private, Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_if_private_then_public_else_public() {
        run_test(Mode::Private, Mode::Public, Mode::Public);
    }

    #[test]
    fn test_if_private_then_public_else_private() {
        run_test(Mode::Private, Mode::Public, Mode::Private);
    }

    #[test]
    fn test_if_private_then_private_else_constant() {
        run_test(Mode::Private, Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_if_private_then_private_else_public() {
        run_test(Mode::Private, Mode::Private, Mode::Public);
    }

    #[test]
    fn test_if_private_then_private_else_private() {
        run_test(Mode::Private, Mode::Private, Mode::Private);
    }
}
