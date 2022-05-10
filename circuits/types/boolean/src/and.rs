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

impl<E: Environment> BitAnd<Boolean<E>> for Boolean<E> {
    type Output = Boolean<E>;

    /// Returns `(self AND other)`.
    fn bitand(self, other: Boolean<E>) -> Self::Output {
        self & &other
    }
}

impl<E: Environment> BitAnd<Boolean<E>> for &Boolean<E> {
    type Output = Boolean<E>;

    /// Returns `(self AND other)`.
    fn bitand(self, other: Boolean<E>) -> Self::Output {
        self & &other
    }
}

impl<E: Environment> BitAnd<&Boolean<E>> for Boolean<E> {
    type Output = Boolean<E>;

    /// Returns `(self AND other)`.
    fn bitand(self, other: &Boolean<E>) -> Self::Output {
        &self & other
    }
}

impl<E: Environment> BitAnd<&Boolean<E>> for &Boolean<E> {
    type Output = Boolean<E>;

    /// Returns `(self AND other)`.
    fn bitand(self, other: &Boolean<E>) -> Self::Output {
        let mut output = self.clone();
        output &= other;
        output
    }
}

impl<E: Environment> BitAndAssign<Boolean<E>> for Boolean<E> {
    /// Sets `self` as `(self AND other)`.
    fn bitand_assign(&mut self, other: Boolean<E>) {
        *self &= &other;
    }
}

impl<E: Environment> BitAndAssign<&Boolean<E>> for Boolean<E> {
    /// Sets `self` as `(self AND other)`.
    fn bitand_assign(&mut self, other: &Boolean<E>) {
        // Stores the bitwise AND of `self` and `other` in `self`.
        *self =
            // Constant `self`
            if self.is_constant() {
                match self.eject_value() {
                    true => other.clone(),
                    false => self.clone(),
                }
            }
            // Constant `other`
            else if other.is_constant() {
                match other.eject_value() {
                    true => self.clone(),
                    false => other.clone(),
                }
            }
            // Variable AND Variable
            else {
                // Declare a new variable with the expected output as witness.
                // Note: The constraint below will ensure `output` is either 0 or 1,
                // assuming `self` and `other` are well-formed (they are either 0 or 1).
                let output = Boolean(
                    E::new_variable(Mode::Private, match self.eject_value() & other.eject_value() {
                        true => E::BaseField::one(),
                        false => E::BaseField::zero(),
                    })
                        .into(),
                );

                // Ensure `self` * `other` = `output`
                // `output` is `1` iff `self` AND `other` are both `1`.
                E::enforce(|| (&*self, other, &output));

                output
            }
    }
}

impl<E: Environment> Metadata<dyn BitAnd<Boolean<E>, Output = Boolean<E>>> for Boolean<E> {
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
            (CircuitType::Constant(a), CircuitType::Constant(b)) => CircuitType::from(a.circuit().bitand(b.circuit())),
            (other_type, CircuitType::Constant(constant)) | (CircuitType::Constant(constant), other_type) => {
                match constant.eject_value() {
                    false => CircuitType::from(Boolean::constant(false)),
                    _ => other_type,
                }
            }
            (_, _) => CircuitType::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;

    fn check_and(name: &str, expected: bool, a: Boolean<Circuit>, b: Boolean<Circuit>) {
        Circuit::scope(name, || {
            let candidate = &a & &b;
            assert_eq!(expected, candidate.eject_value(), "({} AND {})", a.eject_value(), b.eject_value());

            let circuit_type = (CircuitType::from(a), CircuitType::from(b));
            assert_count!(BitAnd(Boolean, Boolean) => Boolean, &circuit_type);
            assert_output_type!(BitAnd(Boolean, Boolean) => Boolean, circuit_type, candidate);
        });
    }

    fn run_test(mode_a: Mode, mode_b: Mode) {
        for first in [true, false] {
            for second in [true, false] {
                let a = Boolean::<Circuit>::new(mode_a, first);
                let b = Boolean::<Circuit>::new(mode_b, second);

                let name = format!("{} AND {}", mode_a, mode_b);
                check_and(&name, first & second, a, b);
            }
        }
    }

    #[test]
    fn test_constant_and_constant() {
        run_test(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_constant_and_public() {
        run_test(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_constant_and_private() {
        run_test(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_public_and_constant() {
        run_test(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_private_and_constant() {
        run_test(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_public_and_public() {
        run_test(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_public_and_private() {
        run_test(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_private_and_public() {
        run_test(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_private_and_private() {
        run_test(Mode::Private, Mode::Private);
    }
}
