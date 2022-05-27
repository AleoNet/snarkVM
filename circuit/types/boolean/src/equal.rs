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

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    fn check_is_equal(
        name: &str,
        expected: bool,
        a: Boolean<Circuit>,
        b: Boolean<Circuit>,
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
    }

    #[test]
    fn test_constant_equals_constant() {
        // false == false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, false);
        let b = Boolean::<Circuit>::new(Mode::Constant, false);
        check_is_equal("false == false", expected, a, b, 0, 0, 0, 0);

        // false == true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Constant, false);
        let b = Boolean::<Circuit>::new(Mode::Constant, true);
        check_is_equal("false == true", expected, a, b, 0, 0, 0, 0);

        // true == false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Constant, true);
        let b = Boolean::<Circuit>::new(Mode::Constant, false);
        check_is_equal("true == false", expected, a, b, 0, 0, 0, 0);

        // true == true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, true);
        let b = Boolean::<Circuit>::new(Mode::Constant, true);
        check_is_equal("true == true", expected, a, b, 0, 0, 0, 0);
    }

    #[test]
    fn test_constant_equals_public() {
        // false == false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, false);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_is_equal("false == false", expected, a, b, 0, 0, 0, 0);

        // false == true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Constant, false);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_is_equal("false == true", expected, a, b, 0, 0, 0, 0);

        // true == false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Constant, true);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_is_equal("true == false", expected, a, b, 0, 0, 0, 0);

        // true == true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, true);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_is_equal("true == true", expected, a, b, 0, 0, 0, 0);
    }

    #[test]
    fn test_constant_equal_private() {
        // false == false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, false);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_is_equal("false == false", expected, a, b, 0, 0, 0, 0);

        // false == true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Constant, false);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_is_equal("false == true", expected, a, b, 0, 0, 0, 0);

        // true == false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Constant, true);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_is_equal("true == false", expected, a, b, 0, 0, 0, 0);

        // true == true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, true);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_is_equal("true == true", expected, a, b, 0, 0, 0, 0);
    }

    #[test]
    fn test_public_equals_constant() {
        // false == false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Constant, false);
        check_is_equal("false == false", expected, a, b, 0, 0, 0, 0);

        // false == true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Constant, true);
        check_is_equal("false == true", expected, a, b, 0, 0, 0, 0);

        // true == false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Constant, false);
        check_is_equal("true == false", expected, a, b, 0, 0, 0, 0);

        // true == true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Constant, true);
        check_is_equal("true == true", expected, a, b, 0, 0, 0, 0);
    }

    #[test]
    fn test_public_equals_public() {
        // false == false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_is_equal("false == false", expected, a, b, 0, 0, 1, 1);

        // false == true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_is_equal("false == true", expected, a, b, 0, 0, 1, 1);

        // true == false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_is_equal("true == false", expected, a, b, 0, 0, 1, 1);

        // true == true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_is_equal("true == true", expected, a, b, 0, 0, 1, 1);
    }

    #[test]
    fn test_public_equals_private() {
        // false == false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_is_equal("false == false", expected, a, b, 0, 0, 1, 1);

        // false == true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_is_equal("false == true", expected, a, b, 0, 0, 1, 1);

        // true == false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_is_equal("true == false", expected, a, b, 0, 0, 1, 1);

        // true == true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_is_equal("true == true", expected, a, b, 0, 0, 1, 1);
    }

    #[test]
    fn test_private_equals_constant() {
        // false == false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Private, false);
        let b = Boolean::<Circuit>::new(Mode::Constant, false);
        check_is_equal("false == false", expected, a, b, 0, 0, 0, 0);

        // false == true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Private, false);
        let b = Boolean::<Circuit>::new(Mode::Constant, true);
        check_is_equal("false == true", expected, a, b, 0, 0, 0, 0);

        // true == false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Constant, false);
        check_is_equal("true == false", expected, a, b, 0, 0, 0, 0);

        // true == true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Constant, true);
        check_is_equal("true == true", expected, a, b, 0, 0, 0, 0);
    }

    #[test]
    fn test_private_equal_public() {
        // false == false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Private, false);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_is_equal("false == false", expected, a, b, 0, 0, 1, 1);

        // false == true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Private, false);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_is_equal("false == true", expected, a, b, 0, 0, 1, 1);

        // true == false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_is_equal("true == false", expected, a, b, 0, 0, 1, 1);

        // true == true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_is_equal("true == true", expected, a, b, 0, 0, 1, 1);
    }

    #[test]
    fn test_private_equals_private() {
        // false == false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Private, false);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_is_equal("false == false", expected, a, b, 0, 0, 1, 1);

        // false == true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Private, false);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_is_equal("false == true", expected, a, b, 0, 0, 1, 1);

        // true == false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_is_equal("true == false", expected, a, b, 0, 0, 1, 1);

        // true == true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_is_equal("true == true", expected, a, b, 0, 0, 1, 1);
    }
}
