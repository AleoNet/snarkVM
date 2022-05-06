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

impl<E: Environment> BitOr<Boolean<E>> for Boolean<E> {
    type Output = Boolean<E>;

    /// Returns `(self OR other)`.
    fn bitor(self, other: Boolean<E>) -> Self::Output {
        self | &other
    }
}

impl<E: Environment> BitOr<Boolean<E>> for &Boolean<E> {
    type Output = Boolean<E>;

    /// Returns `(self OR other)`.
    fn bitor(self, other: Boolean<E>) -> Self::Output {
        self | &other
    }
}

impl<E: Environment> BitOr<&Boolean<E>> for Boolean<E> {
    type Output = Boolean<E>;

    /// Returns `(self OR other)`.
    fn bitor(self, other: &Boolean<E>) -> Self::Output {
        &self | other
    }
}

impl<E: Environment> BitOr<&Boolean<E>> for &Boolean<E> {
    type Output = Boolean<E>;

    /// Returns `(self OR other)`.
    fn bitor(self, other: &Boolean<E>) -> Self::Output {
        let mut output = self.clone();
        output |= other;
        output
    }
}

impl<E: Environment> BitOrAssign<Boolean<E>> for Boolean<E> {
    /// Sets `self` as `(self OR other)`.
    fn bitor_assign(&mut self, other: Boolean<E>) {
        *self |= &other;
    }
}

#[allow(clippy::suspicious_op_assign_impl)]
impl<E: Environment> BitOrAssign<&Boolean<E>> for Boolean<E> {
    /// Sets `self` as `(self OR other)`.
    fn bitor_assign(&mut self, other: &Boolean<E>) {
        // Stores the bitwise OR of `self` and `other` in `self`.
        *self =
            // Constant `self`
            if self.is_constant() {
                match self.eject_value() {
                    true => self.clone(),
                    false => other.clone(),
                }
            }
            // Constant `other`
            else if other.is_constant() {
                match other.eject_value() {
                    true => other.clone(),
                    false => self.clone(),
                }
            }
            // Variable OR Variable
            else {
                // Declare a new variable with the expected output as witness.
                // Note: The constraint below will ensure `output` is either 0 or 1,
                // assuming `self` and `other` are well-formed (they are either 0 or 1).
                let output = Boolean(
                    E::new_variable(Mode::Private, match self.eject_value() | other.eject_value() {
                        true => E::BaseField::one(),
                        false => E::BaseField::zero(),
                    })
                        .into(),
                );

                // Ensure (1 - `self`) * (1 - `other`) = (1 - `output`)
                // `output` is `1` iff `self` OR `other` is `1`.
                E::enforce(|| (E::one() - &self.0, E::one() - &other.0, E::one() - &output.0));

                output
            }
    }
}

impl<E: Environment> Metadata<dyn BitOr<Boolean<E>, Output = Boolean<E>>> for Boolean<E> {
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
            (CircuitType::Constant(_), CircuitType::Constant(_)) => {
                CircuitType::from(case.0.circuit().bitor(case.1.circuit()))
            }
            (other_type, CircuitType::Constant(constant)) | (CircuitType::Constant(constant), other_type) => {
                match constant.eject_value() {
                    true => CircuitType::from(Boolean::constant(true)),
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

    fn check_or(name: &str, expected: bool, a: Boolean<Circuit>, b: Boolean<Circuit>) {
        Circuit::scope(name, || {
            let candidate = &a | &b;
            assert_eq!(expected, candidate.eject_value(), "({} OR {})", a.eject_value(), b.eject_value());

            let circuit_type = (CircuitType::from(a), CircuitType::from(b));
            assert_count!(BitOr(Boolean, Boolean) => Boolean, &circuit_type);
            assert_output_type!(BitOr(Boolean, Boolean) => Boolean, circuit_type, candidate);
        });
    }

    #[test]
    fn test_constant_or_constant() {
        // false OR false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Constant, false);
        let b = Boolean::<Circuit>::new(Mode::Constant, false);
        check_or("false OR false", expected, a, b);

        // false OR true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, false);
        let b = Boolean::<Circuit>::new(Mode::Constant, true);
        check_or("false OR true", expected, a, b);

        // true OR false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, true);
        let b = Boolean::<Circuit>::new(Mode::Constant, false);
        check_or("true OR false", expected, a, b);

        // true OR true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, true);
        let b = Boolean::<Circuit>::new(Mode::Constant, true);
        check_or("true OR true", expected, a, b);
    }

    #[test]
    fn test_constant_or_public() {
        // false OR false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Constant, false);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_or("false OR false", expected, a, b);

        // false OR true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, false);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_or("false OR true", expected, a, b);

        // true OR false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, true);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_or("true OR false", expected, a, b);

        // true OR true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, true);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_or("true OR true", expected, a, b);
    }

    #[test]
    fn test_public_or_constant() {
        // false OR false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Constant, false);
        check_or("false OR false", expected, a, b);

        // false OR true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Constant, true);
        check_or("false OR true", expected, a, b);

        // true OR false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Constant, false);
        check_or("true OR false", expected, a, b);

        // true OR true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Constant, true);
        check_or("true OR true", expected, a, b);
    }

    #[test]
    fn test_public_or_public() {
        // false OR false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_or("false OR false", expected, a, b);

        // false OR true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_or("false OR true", expected, a, b);

        // true OR false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_or("true OR false", expected, a, b);

        // true OR true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_or("true OR true", expected, a, b);
    }

    #[test]
    fn test_public_or_private() {
        // false OR false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_or("false OR false", expected, a, b);

        // false OR true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_or("false OR true", expected, a, b);

        // true OR false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_or("true OR false", expected, a, b);

        // true OR true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_or("true OR true", expected, a, b);
    }

    #[test]
    fn test_private_or_private() {
        // false OR false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Private, false);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_or("false OR false", expected, a, b);

        // false OR true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Private, false);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_or("false OR true", expected, a, b);

        // true OR false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_or("true OR false", expected, a, b);

        // true OR true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_or("true OR true", expected, a, b);
    }
}
