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

impl<E: Environment> BitXor<Boolean<E>> for Boolean<E> {
    type Output = Boolean<E>;

    /// Returns `(self != other)`.
    fn bitxor(self, other: Boolean<E>) -> Self::Output {
        self ^ &other
    }
}

impl<E: Environment> BitXor<Boolean<E>> for &Boolean<E> {
    type Output = Boolean<E>;

    /// Returns `(self != other)`.
    fn bitxor(self, other: Boolean<E>) -> Self::Output {
        self ^ &other
    }
}

impl<E: Environment> BitXor<&Boolean<E>> for Boolean<E> {
    type Output = Boolean<E>;

    /// Returns `(self != other)`.
    fn bitxor(self, other: &Boolean<E>) -> Self::Output {
        &self ^ other
    }
}

impl<E: Environment> BitXor<&Boolean<E>> for &Boolean<E> {
    type Output = Boolean<E>;

    /// Returns `(self != other)`.
    fn bitxor(self, other: &Boolean<E>) -> Self::Output {
        let mut output = self.clone();
        output ^= other;
        output
    }
}

impl<E: Environment> BitXorAssign<Boolean<E>> for Boolean<E> {
    /// Sets `self` as `(self != other)`.
    fn bitxor_assign(&mut self, other: Boolean<E>) {
        *self ^= &other;
    }
}

impl<E: Environment> BitXorAssign<&Boolean<E>> for Boolean<E> {
    /// Sets `self` as `(self != other)`.
    fn bitxor_assign(&mut self, other: &Boolean<E>) {
        // Stores the bitwise XOR of `self` and `other` in `self`.
        *self =
            // Constant `self`
            if self.is_constant() {
                match self.eject_value() {
                    true => !other.clone(),
                    false => other.clone(),
                }
            }
            // Constant `other`
            else if other.is_constant() {
                match other.eject_value() {
                    true => !self.clone(),
                    false => self.clone(),
                }
            }
            // Variable != Variable
            else {
                // Declare a new variable with the expected output as witness.
                // Note: The constraint below will ensure `output` is either 0 or 1,
                // assuming `self` and `other` are well-formed (they are either 0 or 1).
                let output = Boolean(
                    E::new_variable(Mode::Private, match self.eject_value() ^ other.eject_value() {
                        true => E::BaseField::one(),
                        false => E::BaseField::zero(),
                    })
                        .into(),
                );

                //
                // Ensure (`self` + `self`) * (`other`) = (`self` + `other` - `output`)
                // `output` is `1` iff `self` != `other`.
                //
                // As `self` and `other` are enforced to be `Boolean` types,
                // if they are equal, then the `output` is 0,
                // and if they are different, then `output` must be 1.
                //
                // ¬(a ∧ b) ∧ ¬(¬a ∧ ¬b) = c
                //
                // (1 - (a * b)) * (1 - ((1 - a) * (1 - b))) = c
                // (1 - ab) * (1 - (1 - a - b + ab)) = c
                // (1 - ab) * (a + b - ab) = c
                // a + b - ab - (a^2)b - (b^2)a + (a^2)(b^2) = c
                // a + b - ab - ab - ab + ab = c
                // a + b - 2ab = c
                // -2a * b = c - a - b
                // 2a * b = a + b - c
                // (a + a) * b = a + b - c
                //
                E::enforce(|| ((&self.0 + &self.0), other, (&self.0 + &other.0 - &output.0)));

                output
            }
    }
}

impl<E: Environment> Metadata<dyn BitXor<Boolean<E>, Output = Boolean<E>>> for Boolean<E> {
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
            (CircuitType::Constant(a), CircuitType::Constant(b)) => CircuitType::from(a.circuit().bitxor(b.circuit())),
            (other_type, CircuitType::Constant(constant)) | (CircuitType::Constant(constant), other_type) => {
                match constant.eject_value() {
                    false => other_type,
                    true => CircuitType::Private,
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

    fn check_xor(name: &str, expected: bool, a: Boolean<Circuit>, b: Boolean<Circuit>) {
        Circuit::scope(name, || {
            let candidate = &a ^ &b;
            assert_eq!(expected, candidate.eject_value(), "({} XOR {})", a.eject_value(), b.eject_value());

            let circuit_type = (CircuitType::from(a), CircuitType::from(b));
            assert_count!(BitXor(Boolean, Boolean) => Boolean, &circuit_type);
            assert_output_type!(BitXor(Boolean, Boolean) => Boolean, circuit_type, candidate);
        });
    }

    fn run_test(mode_a: Mode, mode_b: Mode) {
        for first in [true, false] {
            for second in [true, false] {
                let a = Boolean::<Circuit>::new(mode_a, first);
                let b = Boolean::<Circuit>::new(mode_b, second);

                let name = format!("{} XOR {}", mode_a, mode_b);
                check_xor(&name, first ^ second, a, b);
            }
        }
    }

    #[test]
    fn test_constant_xor_constant() {
        run_test(Mode::Constant, Mode::Constant)
    }

    #[test]
    fn test_constant_xor_public() {
        run_test(Mode::Constant, Mode::Public)
    }

    #[test]
    fn test_constant_xor_private() {
        run_test(Mode::Constant, Mode::Private)
    }

    #[test]
    fn test_public_xor_constant() {
        run_test(Mode::Public, Mode::Constant)
    }

    #[test]
    fn test_private_xor_constant() {
        run_test(Mode::Private, Mode::Constant)
    }

    #[test]
    fn test_public_xor_public() {
        run_test(Mode::Public, Mode::Public)
    }

    #[test]
    fn test_public_xor_private() {
        run_test(Mode::Public, Mode::Private)
    }

    #[test]
    fn test_private_xor_public() {
        run_test(Mode::Private, Mode::Public)
    }

    #[test]
    fn test_private_xor_private() {
        run_test(Mode::Private, Mode::Private)
    }
}
