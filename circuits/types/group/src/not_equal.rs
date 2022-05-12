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

impl<E: Environment> NotEqual<Self> for Group<E> {
    type Output = Boolean<E>;

    ///
    /// Returns `true` if `self` and `other` are *not* equal.
    ///
    /// This method constructs a boolean that indicates if
    /// `self` and `other ` are *not* equal to each other.
    ///
    /// This method costs 8 constraints.
    ///
    fn is_not_equal(&self, other: &Self) -> Self::Output {
        !self.is_equal(other)
    }
}

impl<E: Environment> Metadata<dyn NotEqual<Group<E>, Output = Boolean<E>>> for Group<E> {
    type Case = (CircuitType<Self>, CircuitType<Self>);
    type OutputType = CircuitType<Boolean<E>>;

    fn count(case: &Self::Case) -> Count {
        match case {
            (CircuitType::Constant(_), CircuitType::Constant(_)) => Count::is(2, 0, 0, 0),
            _ => Count::is(0, 0, 5, 7),
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case {
            (CircuitType::Constant(a), CircuitType::Constant(b)) => {
                CircuitType::from(a.circuit().is_not_equal(&b.circuit()))
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

    const ITERATIONS: u64 = 100;

    fn check_is_not_equal(name: &str, expected: bool, a: &Group<Circuit>, b: &Group<Circuit>) {
        Circuit::scope(name, || {
            let candidate = a.is_not_equal(b);
            assert_eq!(expected, candidate.eject_value(), "({} != {})", a.eject_value(), b.eject_value());

            let case = (CircuitType::from(a), CircuitType::from(b));
            assert_count!(NotEqual(Group, Group) => Boolean, &case);
            assert_output_type!(NotEqual(Group, Group) => Boolean, case, candidate);
        });
    }

    fn run_test(mode_a: Mode, mode_b: Mode) {
        for i in 0..ITERATIONS {
            let first = UniformRand::rand(&mut test_rng());
            let second = UniformRand::rand(&mut test_rng());

            let a = Group::<Circuit>::new(mode_a, first);
            let b = Group::<Circuit>::new(mode_b, second);

            let name = format!("Not Equal: a != b {}", i);
            check_is_not_equal(&name, first != second, &a, &b);

            let name = format!("Not Equal: a != a {}", i);
            check_is_not_equal(&name, false, &a, &a);

            let name = format!("Not Equal: b != b {}", i);
            check_is_not_equal(&name, false, &b, &b);
        }
    }

    #[test]
    fn test_constant_is_not_equal_to_constant() {
        run_test(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_constant_is_not_equal_to_public() {
        run_test(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_constant_is_not_equal_to_private() {
        run_test(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_public_is_not_equal_to_constant() {
        run_test(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_private_is_not_equal_to_constant() {
        run_test(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_public_is_not_equal_to_public() {
        run_test(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_public_is_not_equal_to_private() {
        run_test(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_private_is_not_equal_to_public() {
        run_test(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_private_is_not_equal_to_private() {
        run_test(Mode::Private, Mode::Private);
    }
}
