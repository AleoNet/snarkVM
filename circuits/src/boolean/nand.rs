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

impl<E: Environment> Nand<Self> for Boolean<E> {
    type Boolean = Boolean<E>;
    type Output = Boolean<E>;

    fn nand(&self, other: &Self) -> Self::Output {
        // Constant `self`
        if self.is_constant() {
            match self.to_value() {
                true => !other.clone(),
                false => !self.clone(),
            }
        }
        // Constant `other`
        else if other.is_constant() {
            match other.to_value() {
                true => !self.clone(),
                false => !other.clone(),
            }
        }
        // Variable NAND Variable
        else {
            let output = Boolean::<E>::new(Mode::Private, !(self.to_value() & other.to_value()));

            // Ensure `self` * `other` = (1 - `output`)
            // `output` is `1` iff `self` or `other` is `0`, otherwise `output` is `0`.
            E::enforce(|| (self, other, E::one() - &output.0));

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
            let candidate = a.nand(&b);
            assert_eq!(
                expected,
                candidate.to_value(),
                "{} != {} := ({} NAND {})",
                expected,
                candidate.to_value(),
                a.to_value(),
                b.to_value()
            );

            assert_eq!(num_constants, scope.num_constants_in_scope());
            assert_eq!(num_public, scope.num_public_in_scope());
            assert_eq!(num_private, scope.num_private_in_scope());
            assert_eq!(num_constraints, scope.num_constraints_in_scope());
            assert!(Circuit::is_satisfied());
        });
    }

    #[test]
    fn test_constant_nand_constant() {
        // false NAND false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, false);
        let b = Boolean::<Circuit>::new(Mode::Constant, false);
        check_nor("false NAND false", expected, a, b, 0, 0, 0, 0);

        // false NAND true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, false);
        let b = Boolean::<Circuit>::new(Mode::Constant, true);
        check_nor("false NAND true", expected, a, b, 0, 0, 0, 0);

        // true NAND false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, true);
        let b = Boolean::<Circuit>::new(Mode::Constant, false);
        check_nor("true NAND false", expected, a, b, 0, 0, 0, 0);

        // true NAND true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Constant, true);
        let b = Boolean::<Circuit>::new(Mode::Constant, true);
        check_nor("true NAND true", expected, a, b, 0, 0, 0, 0);
    }

    #[test]
    fn test_constant_nand_public() {
        // false NAND false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, false);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_nor("false NAND false", expected, a, b, 0, 0, 0, 0);

        // false NAND true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, false);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_nor("false NAND true", expected, a, b, 0, 0, 0, 0);

        // true NAND false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, true);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_nor("true NAND false", expected, a, b, 0, 0, 0, 0);

        // true NAND true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Constant, true);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_nor("true NAND true", expected, a, b, 0, 0, 0, 0);
    }

    #[test]
    fn test_public_nand_constant() {
        // false NAND false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Constant, false);
        check_nor("false NAND false", expected, a, b, 0, 0, 0, 0);

        // false NAND true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Constant, true);
        check_nor("false NAND true", expected, a, b, 0, 0, 0, 0);

        // true NAND false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Constant, false);
        check_nor("true NAND false", expected, a, b, 0, 0, 0, 0);

        // true NAND true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Constant, true);
        check_nor("true NAND true", expected, a, b, 0, 0, 0, 0);
    }

    #[test]
    fn test_public_nand_public() {
        // false NAND false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_nor("false NAND false", expected, a, b, 0, 0, 1, 2);

        // false NAND true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_nor("false NAND true", expected, a, b, 0, 0, 1, 2);

        // true NAND false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_nor("true NAND false", expected, a, b, 0, 0, 1, 2);

        // true NAND true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_nor("true NAND true", expected, a, b, 0, 0, 1, 2);
    }

    #[test]
    fn test_public_nand_private() {
        // false NAND false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_nor("false NAND false", expected, a, b, 0, 0, 1, 2);

        // false NAND true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_nor("false NAND true", expected, a, b, 0, 0, 1, 2);

        // true NAND false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_nor("true NAND false", expected, a, b, 0, 0, 1, 2);

        // true NAND true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_nor("true NAND true", expected, a, b, 0, 0, 1, 2);
    }

    #[test]
    fn test_private_nand_private() {
        // false NAND false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Private, false);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_nor("false NAND false", expected, a, b, 0, 0, 1, 2);

        // false NAND true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Private, false);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_nor("false NAND true", expected, a, b, 0, 0, 1, 2);

        // true NAND false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_nor("true NAND false", expected, a, b, 0, 0, 1, 2);

        // true NAND true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_nor("true NAND true", expected, a, b, 0, 0, 1, 2);
    }
}
