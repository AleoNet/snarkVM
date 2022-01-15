// Copyright (C) 2019-2021 Aleo Systems Inc.
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

impl<E: Environment> Nor<Self> for Boolean<E> {
    type Boolean = Boolean<E>;
    type Output = Boolean<E>;

    /// Returns `(NOT a) AND (NOT b)`.
    fn nor(&self, other: &Self) -> Self::Output {
        // Constant `self`
        if self.is_constant() {
            match self.eject_value() {
                true => !self.clone(),
                false => !other.clone(),
            }
        }
        // Constant `other`
        else if other.is_constant() {
            match other.eject_value() {
                true => !other.clone(),
                false => !self.clone(),
            }
        }
        // Variable NOR Variable
        else {
            let output = Boolean::<E>::new(Mode::Private, !self.eject_value() & !other.eject_value());

            // Ensure (1 - `self`) * (1 - `other`) = `output`
            // `output` is `1` iff `self` and `other` are both `0`, otherwise `output` is `0`.
            E::enforce(|| (E::one() - &self.0, E::one() - &other.0, &output));

            Self(output.into())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;

    fn check_nor(
        name: &str,
        expected: bool,
        a: Boolean<Circuit>,
        b: Boolean<Circuit>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, |scope| {
            let candidate = a.nor(&b);
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := ({} NOR {})",
                expected,
                candidate.eject_value(),
                a.eject_value(),
                b.eject_value()
            );

            assert_eq!(num_constants, scope.num_constants_in_scope());
            assert_eq!(num_public, scope.num_public_in_scope());
            assert_eq!(num_private, scope.num_private_in_scope());
            assert_eq!(num_constraints, scope.num_constraints_in_scope());
            assert!(Circuit::is_satisfied());
        });
    }

    #[test]
    fn test_constant_nor_constant() {
        // false NOR false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, false);
        let b = Boolean::<Circuit>::new(Mode::Constant, false);
        check_nor("false NOR false", expected, a, b, 0, 0, 0, 0);

        // false NOR true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Constant, false);
        let b = Boolean::<Circuit>::new(Mode::Constant, true);
        check_nor("false NOR true", expected, a, b, 0, 0, 0, 0);

        // true NOR false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Constant, true);
        let b = Boolean::<Circuit>::new(Mode::Constant, false);
        check_nor("true NOR false", expected, a, b, 0, 0, 0, 0);

        // true NOR true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Constant, true);
        let b = Boolean::<Circuit>::new(Mode::Constant, true);
        check_nor("true NOR true", expected, a, b, 0, 0, 0, 0);
    }

    #[test]
    fn test_constant_nor_public() {
        // false NOR false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, false);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_nor("false NOR false", expected, a, b, 0, 0, 0, 0);

        // false NOR true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Constant, false);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_nor("false NOR true", expected, a, b, 0, 0, 0, 0);

        // true NOR false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Constant, true);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_nor("true NOR false", expected, a, b, 0, 0, 0, 0);

        // true NOR true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Constant, true);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_nor("true NOR true", expected, a, b, 0, 0, 0, 0);
    }

    #[test]
    fn test_public_nor_constant() {
        // false NOR false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Constant, false);
        check_nor("false NOR false", expected, a, b, 0, 0, 0, 0);

        // false NOR true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Constant, true);
        check_nor("false NOR true", expected, a, b, 0, 0, 0, 0);

        // true NOR false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Constant, false);
        check_nor("true NOR false", expected, a, b, 0, 0, 0, 0);

        // true NOR true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Constant, true);
        check_nor("true NOR true", expected, a, b, 0, 0, 0, 0);
    }

    #[test]
    fn test_public_nor_public() {
        // false NOR false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_nor("false NOR false", expected, a, b, 0, 0, 1, 2);

        // false NOR true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_nor("false NOR true", expected, a, b, 0, 0, 1, 2);

        // true NOR false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_nor("true NOR false", expected, a, b, 0, 0, 1, 2);

        // true NOR true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_nor("true NOR true", expected, a, b, 0, 0, 1, 2);
    }

    #[test]
    fn test_public_nor_private() {
        // false NOR false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_nor("false NOR false", expected, a, b, 0, 0, 1, 2);

        // false NOR true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_nor("false NOR true", expected, a, b, 0, 0, 1, 2);

        // true NOR false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_nor("true NOR false", expected, a, b, 0, 0, 1, 2);

        // true NOR true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_nor("true NOR true", expected, a, b, 0, 0, 1, 2);
    }

    #[test]
    fn test_private_nor_private() {
        // false NOR false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Private, false);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_nor("false NOR false", expected, a, b, 0, 0, 1, 2);

        // false NOR true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Private, false);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_nor("false NOR true", expected, a, b, 0, 0, 1, 2);

        // true NOR false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_nor("true NOR false", expected, a, b, 0, 0, 1, 2);

        // true NOR true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_nor("true NOR true", expected, a, b, 0, 0, 1, 2);
    }
}
