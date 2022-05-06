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

impl<E: Environment> Equal<Self> for Scalar<E> {
    type Output = Boolean<E>;

    ///
    /// Returns `true` if `self` and `other` are equal.
    ///
    fn is_equal(&self, other: &Self) -> Self::Output {
        self.to_field().is_equal(&other.to_field())
    }

    ///
    /// Returns `true` if `self` and `other` are *not* equal.
    ///
    fn is_not_equal(&self, other: &Self) -> Self::Output {
        !self.is_equal(other)
    }
}

impl<E: Environment> Metadata<dyn Equal<Scalar<E>, Output = Boolean<E>>> for Scalar<E> {
    type Case = (CircuitType<Self>, CircuitType<Self>);
    type OutputType = CircuitType<Boolean<E>>;

    fn count(case: &Self::Case) -> Count {
        match case.0.is_constant() && case.1.is_constant() {
            true => Count::is(1, 0, 0, 0),
            false => Count::is(0, 0, 2, 3),
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case.0.is_constant() && case.1.is_constant() {
            true => CircuitType::from(case.0.circuit().is_equal(&case.1.circuit())),
            false => CircuitType::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    fn check_is_equal(name: &str, expected: bool, a: Scalar<Circuit>, b: Scalar<Circuit>) {
        Circuit::scope(name, || {
            let candidate = a.is_equal(&b);
            assert_eq!(expected, candidate.eject_value(), "({} == {})", a.eject_value(), b.eject_value());

            let case = (CircuitType::from(a), CircuitType::from(b));
            assert_count!(Equal(Scalar, Scalar) => Boolean, &case);
            assert_output_type!(Equal(Scalar, Scalar) => Boolean, case, candidate);
        });
        Circuit::reset();
    }

    #[test]
    fn test_constant_equals_constant() {
        let first = UniformRand::rand(&mut test_rng());
        let second = UniformRand::rand(&mut test_rng());

        // a == a
        let expected = true;
        let a = Scalar::<Circuit>::new(Mode::Constant, first);
        let b = Scalar::<Circuit>::new(Mode::Constant, first);
        check_is_equal("a == a", expected, a, b);

        // a != b
        let expected = false;
        let a = Scalar::<Circuit>::new(Mode::Constant, first);
        let b = Scalar::<Circuit>::new(Mode::Constant, second);
        check_is_equal("a != b", expected, a, b);
    }

    #[test]
    fn test_constant_equals_public() {
        let first = UniformRand::rand(&mut test_rng());
        let second = UniformRand::rand(&mut test_rng());

        // a == a
        let expected = true;
        let a = Scalar::<Circuit>::new(Mode::Constant, first);
        let b = Scalar::<Circuit>::new(Mode::Public, first);
        check_is_equal("a == a", expected, a, b);

        // a != b
        let expected = false;
        let a = Scalar::<Circuit>::new(Mode::Constant, first);
        let b = Scalar::<Circuit>::new(Mode::Public, second);
        check_is_equal("a != b", expected, a, b);
    }

    #[test]
    fn test_public_equals_constant() {
        let first = UniformRand::rand(&mut test_rng());
        let second = UniformRand::rand(&mut test_rng());

        // a == a
        let expected = true;
        let a = Scalar::<Circuit>::new(Mode::Public, first);
        let b = Scalar::<Circuit>::new(Mode::Constant, first);
        check_is_equal("a == a", expected, a, b);

        // a != b
        let expected = false;
        let a = Scalar::<Circuit>::new(Mode::Public, first);
        let b = Scalar::<Circuit>::new(Mode::Constant, second);
        check_is_equal("a != b", expected, a, b);
    }

    #[test]
    fn test_public_equals_public() {
        let first = UniformRand::rand(&mut test_rng());
        let second = UniformRand::rand(&mut test_rng());

        // a == a
        let expected = true;
        let a = Scalar::<Circuit>::new(Mode::Public, first);
        let b = Scalar::<Circuit>::new(Mode::Public, first);
        check_is_equal("a == a", expected, a, b);

        // a != b
        let expected = false;
        let a = Scalar::<Circuit>::new(Mode::Public, first);
        let b = Scalar::<Circuit>::new(Mode::Public, second);
        check_is_equal("a != b", expected, a, b);
    }

    #[test]
    fn test_public_equals_private() {
        let first = UniformRand::rand(&mut test_rng());
        let second = UniformRand::rand(&mut test_rng());

        // a == a
        let expected = true;
        let a = Scalar::<Circuit>::new(Mode::Public, first);
        let b = Scalar::<Circuit>::new(Mode::Private, first);
        check_is_equal("a == a", expected, a, b);

        // a != b
        let expected = false;
        let a = Scalar::<Circuit>::new(Mode::Public, first);
        let b = Scalar::<Circuit>::new(Mode::Private, second);
        check_is_equal("a != b", expected, a, b);
    }

    #[test]
    fn test_private_equals_private() {
        let first = UniformRand::rand(&mut test_rng());
        let second = UniformRand::rand(&mut test_rng());

        // a == a
        let expected = true;
        let a = Scalar::<Circuit>::new(Mode::Private, first);
        let b = Scalar::<Circuit>::new(Mode::Private, first);
        check_is_equal("a == a", expected, a, b);

        // a != b
        let expected = false;
        let a = Scalar::<Circuit>::new(Mode::Private, first);
        let b = Scalar::<Circuit>::new(Mode::Private, second);
        check_is_equal("a != b", expected, a, b);
    }
}
