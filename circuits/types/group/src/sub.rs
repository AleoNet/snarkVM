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

impl<E: Environment> Sub<Self> for Group<E> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        self - &other
    }
}

impl<E: Environment> Sub<&Self> for Group<E> {
    type Output = Self;

    fn sub(self, other: &Self) -> Self::Output {
        self + -other
    }
}

impl<E: Environment> Sub<&Group<E>> for &Group<E> {
    type Output = Group<E>;

    fn sub(self, other: &Group<E>) -> Self::Output {
        (*self).clone() - other
    }
}

impl<E: Environment> SubAssign<Self> for Group<E> {
    fn sub_assign(&mut self, other: Self) {
        *self -= &other;
    }
}

impl<E: Environment> SubAssign<&Self> for Group<E> {
    fn sub_assign(&mut self, other: &Self) {
        *self = self.clone() + -other;
    }
}

impl<E: Environment> Metadata<dyn Sub<Group<E>, Output = Group<E>>> for Group<E> {
    type Case = (CircuitType<Group<E>>, CircuitType<Group<E>>);
    type OutputType = CircuitType<Group<E>>;

    fn count(case: &Self::Case) -> Count {
        match case {
            (CircuitType::Constant(_), CircuitType::Constant(_)) => Count::is(4, 0, 0, 0),
            (CircuitType::Constant(_), _) | (_, CircuitType::Constant(_)) => Count::is(2, 0, 3, 3),
            (_, _) => Count::is(2, 0, 6, 6),
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case {
            (CircuitType::Constant(a), CircuitType::Constant(b)) => CircuitType::from(a.circuit().sub(b.circuit())),
            (_, _) => CircuitType::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: u64 = 100;

    fn check_sub(name: &str, expected: &<Circuit as Environment>::Affine, a: &Group<Circuit>, b: &Group<Circuit>) {
        Circuit::scope(name, || {
            let candidate = a - b;
            assert_eq!(*expected, candidate.eject_value(), "({} - {})", a.eject_value(), b.eject_value());

            let case = (CircuitType::from(a), CircuitType::from(b));
            assert_count!(Sub(Group, Group) => Group, &case);
            assert_output_type!(Sub(Group, Group) => Group, case, candidate);
        });
    }

    fn check_sub_assign(
        name: &str,
        expected: &<Circuit as Environment>::Affine,
        a: &Group<Circuit>,
        b: &Group<Circuit>,
    ) {
        Circuit::scope(name, || {
            let mut candidate = a.clone();
            candidate -= b;
            assert_eq!(*expected, candidate.eject_value(), "({} - {})", a.eject_value(), b.eject_value());

            let case = (CircuitType::from(a), CircuitType::from(b));
            assert_count!(Sub(Group, Group) => Group, &case);
            assert_output_type!(Sub(Group, Group) => Group, case, candidate);
        });
    }

    fn run_test(mode_a: Mode, mode_b: Mode) {
        for i in 0..ITERATIONS {
            let first = <Circuit as Environment>::Affine::rand(&mut test_rng());
            let second = <Circuit as Environment>::Affine::rand(&mut test_rng());

            let expected = (first.to_projective() - second.to_projective()).into();
            let a = Group::<Circuit>::new(mode_a, first);
            let b = Group::<Circuit>::new(mode_b, second);

            let name = format!("Sub: a - b {}", i);
            check_sub(&name, &expected, &a, &b);
            let name = format!("SubAssign: a - b {}", i);
            check_sub_assign(&name, &expected, &a, &b);
        }
    }

    #[test]
    fn test_constant_minus_constant() {
        run_test(Mode::Constant, Mode::Constant)
    }

    #[test]
    fn test_constant_minus_public() {
        run_test(Mode::Constant, Mode::Public)
    }

    #[test]
    fn test_constant_minus_private() {
        run_test(Mode::Constant, Mode::Private)
    }

    #[test]
    fn test_public_minus_constant() {
        run_test(Mode::Public, Mode::Constant)
    }

    #[test]
    fn test_public_minus_public() {
        run_test(Mode::Public, Mode::Public)
    }

    #[test]
    fn test_public_minus_private() {
        run_test(Mode::Public, Mode::Private)
    }

    #[test]
    fn test_private_minus_constant() {
        run_test(Mode::Private, Mode::Constant)
    }

    #[test]
    fn test_private_minus_public() {
        run_test(Mode::Private, Mode::Public)
    }

    #[test]
    fn test_private_minus_private() {
        run_test(Mode::Private, Mode::Private)
    }

    #[test]
    fn test_sub_matches() {
        // Sample two random elements.
        let a: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
        let b: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
        let expected = a.to_projective() - b.to_projective();

        // Constant
        let first = Group::<Circuit>::new(Mode::Constant, a);
        let second = Group::<Circuit>::new(Mode::Constant, b);
        let candidate_a = first - second;
        assert_eq!(expected, candidate_a.eject_value());

        // Private
        let first = Group::<Circuit>::new(Mode::Private, a);
        let second = Group::<Circuit>::new(Mode::Private, b);
        let candidate_b = first - second;
        assert_eq!(expected, candidate_b.eject_value());
    }
}
