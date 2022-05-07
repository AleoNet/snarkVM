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

// TODO: Split into multiple traits for coherency with metadata.

impl<E: Environment> Equal<Self> for Boolean<E> {
    type Output = Boolean<E>;

    /// Returns `true` if `self` and `other` are equal.
    fn is_equal(&self, other: &Self) -> Self::Output {
        !self.is_not_equal(other)
    }

    /// Returns `true` if `self` and `other` are *not* equal.
    fn is_not_equal(&self, other: &Self) -> Self::Output {
        self ^ other
    }
}

impl<E: Environment> Metadata<dyn Equal<Boolean<E>, Output = Boolean<E>>> for Boolean<E> {
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
                CircuitType::from(case.0.circuit().is_equal(case.1.circuit()))
            }
            (CircuitType::Constant(constant), other_type) | (other_type, CircuitType::Constant(constant)) => {
                match constant.eject_value() {
                    true => other_type,
                    false => CircuitType::Private,
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

    fn check_is_equal(name: &str, expected: bool, a: Boolean<Circuit>, b: Boolean<Circuit>) {
        Circuit::scope(name, || {
            let candidate = a.is_equal(&b);
            assert_eq!(expected, candidate.eject_value(), "({} == {})", a.eject_value(), b.eject_value());

            let circuit_type = (CircuitType::from(a), CircuitType::from(b));
            assert_count!(Equal(Boolean, Boolean) => Boolean, &circuit_type);
            assert_output_type!(Equal(Boolean, Boolean) => Boolean, circuit_type, candidate);
        });
    }

    fn run_test(mode_a: Mode, mode_b: Mode) {
        for first in [true, false] {
            for second in [true, false] {
                let a = Boolean::<Circuit>::new(mode_a, first);
                let b = Boolean::<Circuit>::new(mode_b, second);

                let name = format!("{} == {}", mode_a, mode_b);
                check_is_equal(&name, first == second, a, b);
            }
        }
    }

    #[test]
    fn test_constant_is_equal_constant() {
        run_test(Mode::Constant, Mode::Constant)
    }

    #[test]
    fn test_constant_is_equal_public() {
        run_test(Mode::Constant, Mode::Public)
    }

    #[test]
    fn test_constant_is_equal_private() {
        run_test(Mode::Constant, Mode::Private)
    }

    #[test]
    fn test_public_is_equal_constant() {
        run_test(Mode::Public, Mode::Constant)
    }

    #[test]
    fn test_private_is_equal_constant() {
        run_test(Mode::Private, Mode::Constant)
    }

    #[test]
    fn test_public_is_equal_public() {
        run_test(Mode::Public, Mode::Public)
    }

    #[test]
    fn test_public_is_equal_private() {
        run_test(Mode::Public, Mode::Private)
    }

    #[test]
    fn test_private_is_equal_public() {
        run_test(Mode::Private, Mode::Public)
    }

    #[test]
    fn test_private_is_equal_private() {
        run_test(Mode::Private, Mode::Private)
    }
}
