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
        self.field.is_equal(&other.field)
    }

    ///
    /// Returns `true` if `self` and `other` are *not* equal.
    ///
    fn is_not_equal(&self, other: &Self) -> Self::Output {
        !self.is_equal(other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    fn check_is_equal(
        name: &str,
        expected: bool,
        a: Scalar<Circuit>,
        b: Scalar<Circuit>,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        Circuit::scope(name, || {
            let candidate = a.is_equal(&b);
            assert_eq!(expected, candidate.eject_value(), "({} == {})", a.eject_value(), b.eject_value());
            assert_scope!(num_constants, num_public, num_private, num_constraints);
        });
        Circuit::reset();
    }

    #[test]
    fn test_constant_equals_constant() {
        let first = Uniform::rand(&mut test_rng());
        let second = Uniform::rand(&mut test_rng());

        // a == a
        let expected = true;
        let a = Scalar::<Circuit>::new(Mode::Constant, first);
        let b = Scalar::<Circuit>::new(Mode::Constant, first);
        check_is_equal("a == a", expected, a, b, 1, 0, 0, 0);

        // a != b
        let expected = false;
        let a = Scalar::<Circuit>::new(Mode::Constant, first);
        let b = Scalar::<Circuit>::new(Mode::Constant, second);
        check_is_equal("a != b", expected, a, b, 1, 0, 0, 0);
    }

    #[test]
    fn test_constant_equals_public() {
        let first = Uniform::rand(&mut test_rng());
        let second = Uniform::rand(&mut test_rng());

        // a == a
        let expected = true;
        let a = Scalar::<Circuit>::new(Mode::Constant, first);
        let b = Scalar::<Circuit>::new(Mode::Public, first);
        check_is_equal("a == a", expected, a, b, 0, 0, 2, 3);

        // a != b
        let expected = false;
        let a = Scalar::<Circuit>::new(Mode::Constant, first);
        let b = Scalar::<Circuit>::new(Mode::Public, second);
        check_is_equal("a != b", expected, a, b, 0, 0, 2, 3);
    }

    #[test]
    fn test_public_equals_constant() {
        let first = Uniform::rand(&mut test_rng());
        let second = Uniform::rand(&mut test_rng());

        // a == a
        let expected = true;
        let a = Scalar::<Circuit>::new(Mode::Public, first);
        let b = Scalar::<Circuit>::new(Mode::Constant, first);
        check_is_equal("a == a", expected, a, b, 0, 0, 2, 3);

        // a != b
        let expected = false;
        let a = Scalar::<Circuit>::new(Mode::Public, first);
        let b = Scalar::<Circuit>::new(Mode::Constant, second);
        check_is_equal("a != b", expected, a, b, 0, 0, 2, 3);
    }

    #[test]
    fn test_public_equals_public() {
        let first = Uniform::rand(&mut test_rng());
        let second = Uniform::rand(&mut test_rng());

        // a == a
        let expected = true;
        let a = Scalar::<Circuit>::new(Mode::Public, first);
        let b = Scalar::<Circuit>::new(Mode::Public, first);
        check_is_equal("a == a", expected, a, b, 0, 0, 2, 3);

        // a != b
        let expected = false;
        let a = Scalar::<Circuit>::new(Mode::Public, first);
        let b = Scalar::<Circuit>::new(Mode::Public, second);
        check_is_equal("a != b", expected, a, b, 0, 0, 2, 3);
    }

    #[test]
    fn test_public_equals_private() {
        let first = Uniform::rand(&mut test_rng());
        let second = Uniform::rand(&mut test_rng());

        // a == a
        let expected = true;
        let a = Scalar::<Circuit>::new(Mode::Public, first);
        let b = Scalar::<Circuit>::new(Mode::Private, first);
        check_is_equal("a == a", expected, a, b, 0, 0, 2, 3);

        // a != b
        let expected = false;
        let a = Scalar::<Circuit>::new(Mode::Public, first);
        let b = Scalar::<Circuit>::new(Mode::Private, second);
        check_is_equal("a != b", expected, a, b, 0, 0, 2, 3);
    }

    #[test]
    fn test_private_equals_private() {
        let first = Uniform::rand(&mut test_rng());
        let second = Uniform::rand(&mut test_rng());

        // a == a
        let expected = true;
        let a = Scalar::<Circuit>::new(Mode::Private, first);
        let b = Scalar::<Circuit>::new(Mode::Private, first);
        check_is_equal("a == a", expected, a, b, 0, 0, 2, 3);

        // a != b
        let expected = false;
        let a = Scalar::<Circuit>::new(Mode::Private, first);
        let b = Scalar::<Circuit>::new(Mode::Private, second);
        check_is_equal("a != b", expected, a, b, 0, 0, 2, 3);
    }
}
