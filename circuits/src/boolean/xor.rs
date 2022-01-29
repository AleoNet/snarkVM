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

impl<E: Environment> Xor<Self> for Boolean<E> {
    type Boolean = Boolean<E>;
    type Output = Boolean<E>;

    /// Returns `(a != b)`.
    fn xor(&self, other: &Self) -> Self::Output {
        // Constant `self`
        if self.is_constant() {
            match self.eject_value() {
                true => !other.clone(),
                false => other.clone(),
            }
        }
        // Constant `other`
        else if other.is_constant() {
            match other.eject_value() {
                true => !self.clone(),
                false => self.clone(),
            }
        }
        // Variable != Variable
        else {
            // Declare a new variable with the expected output as witness.
            // Note: The constraint below will ensure `output` is either 0 or 1,
            // assuming `self` and `other` are well-formed (they are either 0 or 1).
            let output = Boolean(
                E::new_variable(Mode::Private, match self.eject_value() ^ other.eject_value() {
                    true => E::BaseField::one(),
                    false => E::BaseField::zero(),
                })
                .into(),
            );

            //
            // Ensure (`self` + `self`) * (`other`) = (`self` + `other` - `output`)
            // `output` is `1` iff `self` != `other`.
            //
            // As `self` and `other` are enforced to be `Boolean` types,
            // if they are equal, then the `output` is 0,
            // and if they are different, then `output` must be 1.
            //
            // ¬(a ∧ b) ∧ ¬(¬a ∧ ¬b) = c
            //
            // (1 - (a * b)) * (1 - ((1 - a) * (1 - b))) = c
            // (1 - ab) * (1 - (1 - a - b + ab)) = c
            // (1 - ab) * (a + b - ab) = c
            // a + b - ab - (a^2)b - (b^2)a + (a^2)(b^2) = c
            // a + b - ab - ab - ab + ab = c
            // a + b - 2ab = c
            // -2a * b = c - a - b
            // 2a * b = a + b - c
            // (a + a) * b = a + b - c
            //
            E::enforce(|| ((&self.0 + &self.0), other, (&self.0 + &other.0 - &output.0)));

            output
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;

    fn check_xor(
        name: &str,
        expected: bool,
        a: Boolean<Circuit>,
        b: Boolean<Circuit>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, || {
            let candidate = a.xor(&b);
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := ({} != {})",
                expected,
                candidate.eject_value(),
                a.eject_value(),
                b.eject_value()
            );

            assert_eq!(num_constants, Circuit::num_constants_in_scope(), "(num_constants)");
            assert_eq!(num_public, Circuit::num_public_in_scope(), "(num_public)");
            assert_eq!(num_private, Circuit::num_private_in_scope(), "(num_private)");
            assert_eq!(num_constraints, Circuit::num_constraints_in_scope(), "(num_constraints)");
            assert!(Circuit::is_satisfied(), "(is_satisfied)");
        });
    }

    #[test]
    fn test_constant_xor_constant() {
        // false != false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Constant, false);
        let b = Boolean::<Circuit>::new(Mode::Constant, false);
        check_xor("false != false", expected, a, b, 0, 0, 0, 0);

        // false != true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, false);
        let b = Boolean::<Circuit>::new(Mode::Constant, true);
        check_xor("false != true", expected, a, b, 0, 0, 0, 0);

        // true != false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, true);
        let b = Boolean::<Circuit>::new(Mode::Constant, false);
        check_xor("true != false", expected, a, b, 0, 0, 0, 0);

        // true != true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Constant, true);
        let b = Boolean::<Circuit>::new(Mode::Constant, true);
        check_xor("true != true", expected, a, b, 0, 0, 0, 0);
    }

    #[test]
    fn test_constant_xor_public() {
        // false != false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Constant, false);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_xor("false != false", expected, a, b, 0, 0, 0, 0);

        // false != true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, false);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_xor("false != true", expected, a, b, 0, 0, 0, 0);

        // true != false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Constant, true);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_xor("true != false", expected, a, b, 0, 0, 0, 0);

        // true != true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Constant, true);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_xor("true != true", expected, a, b, 0, 0, 0, 0);
    }

    #[test]
    fn test_public_xor_constant() {
        // false != false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Constant, false);
        check_xor("false != false", expected, a, b, 0, 0, 0, 0);

        // false != true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Constant, true);
        check_xor("false != true", expected, a, b, 0, 0, 0, 0);

        // true != false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Constant, false);
        check_xor("true != false", expected, a, b, 0, 0, 0, 0);

        // true != true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Constant, true);
        check_xor("true != true", expected, a, b, 0, 0, 0, 0);
    }

    #[test]
    fn test_public_xor_public() {
        // false != false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_xor("false != false", expected, a, b, 0, 0, 1, 1);

        // false != true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_xor("false != true", expected, a, b, 0, 0, 1, 1);

        // true != false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_xor("true != false", expected, a, b, 0, 0, 1, 1);

        // true != true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_xor("true != true", expected, a, b, 0, 0, 1, 1);
    }

    #[test]
    fn test_public_xor_private() {
        // false != false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_xor("false != false", expected, a, b, 0, 0, 1, 1);

        // false != true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_xor("false != true", expected, a, b, 0, 0, 1, 1);

        // true != false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_xor("true != false", expected, a, b, 0, 0, 1, 1);

        // true != true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_xor("true != true", expected, a, b, 0, 0, 1, 1);
    }

    #[test]
    fn test_private_xor_private() {
        // false != false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Private, false);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_xor("false != false", expected, a, b, 0, 0, 1, 1);

        // false != true
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Private, false);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_xor("false != true", expected, a, b, 0, 0, 1, 1);

        // true != false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_xor("true != false", expected, a, b, 0, 0, 1, 1);

        // true != true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_xor("true != true", expected, a, b, 0, 0, 1, 1);
    }
}
