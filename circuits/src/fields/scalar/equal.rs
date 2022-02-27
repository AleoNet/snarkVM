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

use itertools::Itertools;

impl<E: Environment> Equal<Self> for ScalarField<E> {
    type Boolean = Boolean<E>;

    ///
    /// Returns `true` if `self` and `other` are equal.
    ///
    fn is_eq(&self, other: &Self) -> Self::Boolean {
        let mut output = Boolean::new(Mode::Constant, true);

        for (a, b) in self.0.iter().zip_eq(other.0.iter()) {
            output &= a.is_eq(b);
        }

        output
    }

    ///
    /// Returns `true` if `self` and `other` are *not* equal.
    ///
    fn is_neq(&self, other: &Self) -> Self::Boolean {
        !self.is_eq(other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_circuit, Circuit};
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    fn check_is_eq(
        name: &str,
        expected: bool,
        a: ScalarField<Circuit>,
        b: ScalarField<Circuit>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, || {
            let candidate = a.is_eq(&b);
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} == {} := ({} == {})",
                expected,
                candidate.eject_value(),
                a.eject_value(),
                b.eject_value()
            );
            assert_circuit!(num_constants, num_public, num_private, num_constraints);
        });
    }

    #[test]
    fn test_constant_equals_constant() {
        let first = UniformRand::rand(&mut thread_rng());
        let second = UniformRand::rand(&mut thread_rng());

        // a == a
        let expected = true;
        let a = ScalarField::<Circuit>::new(Mode::Constant, first);
        let b = ScalarField::<Circuit>::new(Mode::Constant, first);
        check_is_eq("a == a", expected, a, b, 1, 0, 0, 0);

        // a != b
        let expected = false;
        let a = ScalarField::<Circuit>::new(Mode::Constant, first);
        let b = ScalarField::<Circuit>::new(Mode::Constant, second);
        check_is_eq("a != b", expected, a, b, 1, 0, 0, 0);
    }

    #[test]
    fn test_constant_equals_public() {
        let first = UniformRand::rand(&mut thread_rng());
        let second = UniformRand::rand(&mut thread_rng());

        // a == a
        let expected = true;
        let a = ScalarField::<Circuit>::new(Mode::Constant, first);
        let b = ScalarField::<Circuit>::new(Mode::Public, first);
        check_is_eq("a == a", expected, a, b, 1, 0, 250, 250);

        // a != b
        let expected = false;
        let a = ScalarField::<Circuit>::new(Mode::Constant, first);
        let b = ScalarField::<Circuit>::new(Mode::Public, second);
        check_is_eq("a != b", expected, a, b, 1, 0, 250, 250);
    }

    #[test]
    fn test_public_equals_constant() {
        let first = UniformRand::rand(&mut thread_rng());
        let second = UniformRand::rand(&mut thread_rng());

        // a == a
        let expected = true;
        let a = ScalarField::<Circuit>::new(Mode::Public, first);
        let b = ScalarField::<Circuit>::new(Mode::Constant, first);
        check_is_eq("a == a", expected, a, b, 1, 0, 250, 250);

        // a != b
        let expected = false;
        let a = ScalarField::<Circuit>::new(Mode::Public, first);
        let b = ScalarField::<Circuit>::new(Mode::Constant, second);
        check_is_eq("a != b", expected, a, b, 1, 0, 250, 250);
    }

    #[test]
    fn test_public_equals_public() {
        let first = UniformRand::rand(&mut thread_rng());
        let second = UniformRand::rand(&mut thread_rng());

        // a == a
        let expected = true;
        let a = ScalarField::<Circuit>::new(Mode::Public, first);
        let b = ScalarField::<Circuit>::new(Mode::Public, first);
        check_is_eq("a == a", expected, a, b, 1, 0, 501, 501);

        // a != b
        let expected = false;
        let a = ScalarField::<Circuit>::new(Mode::Public, first);
        let b = ScalarField::<Circuit>::new(Mode::Public, second);
        check_is_eq("a != b", expected, a, b, 1, 0, 501, 501);
    }

    #[test]
    fn test_public_equals_private() {
        let first = UniformRand::rand(&mut thread_rng());
        let second = UniformRand::rand(&mut thread_rng());

        // a == a
        let expected = true;
        let a = ScalarField::<Circuit>::new(Mode::Public, first);
        let b = ScalarField::<Circuit>::new(Mode::Private, first);
        check_is_eq("a == a", expected, a, b, 1, 0, 501, 501);

        // a != b
        let expected = false;
        let a = ScalarField::<Circuit>::new(Mode::Public, first);
        let b = ScalarField::<Circuit>::new(Mode::Private, second);
        check_is_eq("a != b", expected, a, b, 1, 0, 501, 501);
    }

    #[test]
    fn test_private_equals_private() {
        let first = UniformRand::rand(&mut thread_rng());
        let second = UniformRand::rand(&mut thread_rng());

        // a == a
        let expected = true;
        let a = ScalarField::<Circuit>::new(Mode::Private, first);
        let b = ScalarField::<Circuit>::new(Mode::Private, first);
        check_is_eq("a == a", expected, a, b, 1, 0, 501, 501);

        // a != b
        let expected = false;
        let a = ScalarField::<Circuit>::new(Mode::Private, first);
        let b = ScalarField::<Circuit>::new(Mode::Private, second);
        check_is_eq("a != b", expected, a, b, 1, 0, 501, 501);
    }
}
