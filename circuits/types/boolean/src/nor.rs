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

impl<E: Environment> Nor<Self> for Boolean<E> {
    type Output = Boolean<E>;

    /// Returns `(NOT a) AND (NOT b)`.
    fn nor(&self, other: &Self) -> Self::Output {
        // Constant `self`
        if self.is_constant() {
            match self.eject_value() {
                true => !self.clone(),
                false => !other.clone(),
            }
        }
        // Constant `other`
        else if other.is_constant() {
            match other.eject_value() {
                true => !other.clone(),
                false => !self.clone(),
            }
        }
        // Variable NOR Variable
        else {
            // Declare a new variable with the expected output as witness.
            // Note: The constraint below will ensure `output` is either 0 or 1,
            // assuming `self` and `other` are well-formed (they are either 0 or 1).
            let output = Boolean(
                E::new_variable(Mode::Private, match !self.eject_value() & !other.eject_value() {
                    true => E::BaseField::one(),
                    false => E::BaseField::zero(),
                })
                .into(),
            );

            // Ensure (1 - `self`) * (1 - `other`) = `output`
            // `output` is `1` iff `self` and `other` are both `0`, otherwise `output` is `0`.
            E::enforce(|| (E::one() - &self.0, E::one() - &other.0, &output));

            output
        }
    }
}

impl<E: Environment> Metadata<dyn Nor<Boolean<E>, Output = Boolean<E>>> for Boolean<E> {
    type Case = (CircuitType<Boolean<E>>, CircuitType<Boolean<E>>);
    type OutputType = CircuitType<Boolean<E>>;

    fn count(case: &Self::Case) -> Count {
        match case.0.is_constant() || case.1.is_constant() {
            true => Count::is(0, 0, 0, 0),
            false => Count::is(0, 0, 1, 1),
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case {
            (CircuitType::Constant(a), CircuitType::Constant(b)) => CircuitType::from(a.circuit().nor(&b.circuit())),
            (CircuitType::Constant(constant), _) | (_, CircuitType::Constant(constant)) => match constant.eject_value()
            {
                true => CircuitType::from(Boolean::constant(false)),
                false => CircuitType::Private,
            },
            (_, _) => CircuitType::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;

    fn check_nor(name: &str, expected: bool, a: Boolean<Circuit>, b: Boolean<Circuit>) {
        Circuit::scope(name, || {
            let candidate = (&a).nor(&b);
            assert_eq!(expected, candidate.eject_value(), "({} NOR {})", a.eject_value(), b.eject_value());

            let circuit_type = (CircuitType::from(a), CircuitType::from(b));
            assert_count!(Nor(Boolean, Boolean) => Boolean, &circuit_type);
            assert_output_type!(Nor(Boolean, Boolean) => Boolean, circuit_type, candidate);
        });
        Circuit::reset();
    }

    fn run_test(mode_a: Mode, mode_b: Mode) {
        for first in [true, false] {
            for second in [true, false] {
                let a = Boolean::<Circuit>::new(mode_a, first);
                let b = Boolean::<Circuit>::new(mode_b, second);

                let name = format!("{} NOR {}", mode_a, mode_b);
                check_nor(&name, (!first) & (!second), a, b);
            }
        }
    }

    #[test]
    fn test_constant_nor_constant() {
        run_test(Mode::Constant, Mode::Constant)
    }

    #[test]
    fn test_constant_nor_public() {
        run_test(Mode::Constant, Mode::Public)
    }

    #[test]
    fn test_constant_nor_private() {
        run_test(Mode::Constant, Mode::Private)
    }

    #[test]
    fn test_public_nor_constant() {
        run_test(Mode::Public, Mode::Constant)
    }

    #[test]
    fn test_private_nor_constant() {
        run_test(Mode::Private, Mode::Constant)
    }

    #[test]
    fn test_public_nor_public() {
        run_test(Mode::Public, Mode::Public)
    }

    #[test]
    fn test_public_nor_private() {
        run_test(Mode::Public, Mode::Private)
    }

    #[test]
    fn test_private_nor_public() {
        run_test(Mode::Private, Mode::Public)
    }

    #[test]
    fn test_private_nor_private() {
        run_test(Mode::Private, Mode::Private)
    }
}
