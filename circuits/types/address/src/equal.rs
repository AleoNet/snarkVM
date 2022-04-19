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

impl<E: Environment> Equal<Self> for Address<E> {
    type Boolean = Boolean<E>;

    /// Returns `true` if `self` and `other` are equal.
    fn is_equal(&self, other: &Self) -> Self::Boolean {
        self.0.is_equal(&other.0)
    }

    /// Returns `true` if `self` and `other` are *not* equal.
    fn is_not_equal(&self, other: &Self) -> Self::Boolean {
        self.0.is_not_equal(&other.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 100;

    fn check_is_equal(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let rng = &mut test_rng();

        for i in 0..ITERATIONS {
            // Sample two random elements.
            let a = Address::<Circuit>::new(mode_a, UniformRand::rand(rng));
            let b = Address::<Circuit>::new(mode_b, UniformRand::rand(rng));

            Circuit::scope(&format!("{mode_a} {mode_a} {i}"), || {
                let equals = a.is_equal(&a);
                assert!(equals.eject_value());
            });

            Circuit::scope(&format!("{mode_a} {mode_b} {i}"), || {
                let equals = a.is_equal(&b);
                assert!(!equals.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    fn check_is_not_equal(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let rng = &mut test_rng();

        for i in 0..ITERATIONS {
            // Sample two random elements.
            let a = Address::<Circuit>::new(mode_a, UniformRand::rand(rng));
            let b = Address::<Circuit>::new(mode_b, UniformRand::rand(rng));

            Circuit::scope(&format!("{mode_a} {mode_a} {i}"), || {
                let equals = a.is_not_equal(&a);
                assert!(!equals.eject_value());
            });

            Circuit::scope(&format!("{mode_a} {mode_b} {i}"), || {
                let equals = a.is_not_equal(&b);
                assert!(equals.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    #[test]
    fn test_is_equal() {
        check_is_equal(Mode::Constant, Mode::Constant, 2, 0, 0, 0);
        check_is_equal(Mode::Constant, Mode::Public, 0, 0, 5, 7);
        check_is_equal(Mode::Constant, Mode::Private, 0, 0, 5, 7);
        check_is_equal(Mode::Public, Mode::Constant, 0, 0, 5, 7);
        check_is_equal(Mode::Private, Mode::Constant, 0, 0, 5, 7);
        check_is_equal(Mode::Public, Mode::Public, 0, 0, 5, 7);
        check_is_equal(Mode::Public, Mode::Private, 0, 0, 5, 7);
        check_is_equal(Mode::Private, Mode::Public, 0, 0, 5, 7);
        check_is_equal(Mode::Private, Mode::Private, 0, 0, 5, 7);
    }

    #[test]
    fn test_is_not_equal() {
        check_is_not_equal(Mode::Constant, Mode::Constant, 2, 0, 0, 0);
        check_is_not_equal(Mode::Constant, Mode::Public, 0, 0, 5, 7);
        check_is_not_equal(Mode::Constant, Mode::Private, 0, 0, 5, 7);
        check_is_not_equal(Mode::Public, Mode::Constant, 0, 0, 5, 7);
        check_is_not_equal(Mode::Private, Mode::Constant, 0, 0, 5, 7);
        check_is_not_equal(Mode::Public, Mode::Public, 0, 0, 5, 7);
        check_is_not_equal(Mode::Public, Mode::Private, 0, 0, 5, 7);
        check_is_not_equal(Mode::Private, Mode::Public, 0, 0, 5, 7);
        check_is_not_equal(Mode::Private, Mode::Private, 0, 0, 5, 7);
    }
}
