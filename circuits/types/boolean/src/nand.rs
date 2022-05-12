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

impl<E: Environment> Nand<Self> for Boolean<E> {
    type Output = Boolean<E>;

    /// Returns `NOT (a AND b)`.
    fn nand(&self, other: &Self) -> Self::Output {
        // Constant `self`
        if self.is_constant() {
            match self.eject_value() {
                true => !other.clone(),
                false => !self.clone(),
            }
        }
        // Constant `other`
        else if other.is_constant() {
            match other.eject_value() {
                true => !self.clone(),
                false => !other.clone(),
            }
        }
        // Variable NAND Variable
        else {
            // Declare a new variable with the expected output as witness.
            // Note: The constraint below will ensure `output` is either 0 or 1,
            // assuming `self` and `other` are well-formed (they are either 0 or 1).
            let output = Boolean(
                E::new_variable(Mode::Private, match !(self.eject_value() & other.eject_value()) {
                    true => E::BaseField::one(),
                    false => E::BaseField::zero(),
                })
                .into(),
            );

            // Ensure `self` * `other` = (1 - `output`)
            // `output` is `1` iff `self` or `other` is `0`, otherwise `output` is `0`.
            E::enforce(|| (self, other, E::one() - &output.0));

            output
        }
    }
}

impl<E: Environment> Metadata<dyn Nand<Boolean<E>, Output = Boolean<E>>> for Boolean<E> {
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
            (CircuitType::Constant(a), CircuitType::Constant(b)) => CircuitType::from(a.circuit().nand(&b.circuit())),
            (_, CircuitType::Constant(constant)) | (CircuitType::Constant(constant), _) => match constant.eject_value()
            {
                false => CircuitType::from(Boolean::constant(true)),
                _ => CircuitType::Private,
            },
            (_, _) => CircuitType::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;

    fn check_nand(name: &str, expected: bool, a: Boolean<Circuit>, b: Boolean<Circuit>) {
        Circuit::scope(name, || {
            let candidate = a.nand(&b);
            assert_eq!(expected, candidate.eject_value(), "({} NAND {})", a.eject_value(), b.eject_value());

            let circuit_type = (CircuitType::from(a), CircuitType::from(b));
            assert_count!(Nand(Boolean, Boolean) => Boolean, &circuit_type);
            assert_output_type!(Nand(Boolean, Boolean) => Boolean, circuit_type, candidate);
        });
    }

    fn run_test(mode_a: Mode, mode_b: Mode) {
        for first in [true, false] {
            for second in [true, false] {
                let a = Boolean::<Circuit>::new(mode_a, first);
                let b = Boolean::<Circuit>::new(mode_b, second);

                let name = format!("{} NAND {}", mode_a, mode_b);
                check_nand(&name, !(first & second), a, b);
            }
        }
    }

    #[test]
    fn test_constant_nand_constant() {
        run_test(Mode::Constant, Mode::Constant)
    }

    #[test]
    fn test_constant_nand_public() {
        run_test(Mode::Constant, Mode::Public)
    }

    #[test]
    fn test_constant_nand_private() {
        run_test(Mode::Constant, Mode::Private)
    }

    #[test]
    fn test_public_nand_constant() {
        run_test(Mode::Public, Mode::Constant)
    }

    #[test]
    fn test_private_nand_constant() {
        run_test(Mode::Private, Mode::Constant)
    }

    #[test]
    fn test_public_nand_public() {
        run_test(Mode::Public, Mode::Public)
    }

    #[test]
    fn test_public_nand_private() {
        run_test(Mode::Public, Mode::Private)
    }

    #[test]
    fn test_private_nand_public() {
        run_test(Mode::Private, Mode::Public)
    }

    #[test]
    fn test_private_nand_private() {
        run_test(Mode::Private, Mode::Private)
    }
}
