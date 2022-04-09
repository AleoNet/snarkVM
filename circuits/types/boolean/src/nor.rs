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

use snarkvm_circuits_environment::Count;
use snarkvm_utilities::generate_metadata_impl;

impl<E: Environment> Nor<Self> for Boolean<E> {
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
            // Declare a new variable with the expected output as witness.
            // Note: The constraint below will ensure `output` is either 0 or 1,
            // assuming `self` and `other` are well-formed (they are either 0 or 1).
            let output = Boolean(
                E::new_variable(Mode::Private, match !self.eject_value() & !other.eject_value() {
                    true => E::BaseField::one(),
                    false => E::BaseField::zero(),
                })
                .into(),
            );

            // Ensure (1 - `self`) * (1 - `other`) = `output`
            // `output` is `1` iff `self` and `other` are both `0`, otherwise `output` is `0`.
            E::enforce(|| (E::one() - &self.0, E::one() - &other.0, &output));

            output
        }
    }
}

#[generate_metadata_impl(generate = true, runs = 128)]
impl<E: Environment> MetadataForOp<dyn Nor<Boolean<E>, Output = Boolean<E>>> for Boolean<E> {
    type Case = (Mode, Mode);

    fn count(input: &Self::Case) -> Count {
        match input.0.is_constant() || input.1.is_constant() {
            true => Count::exact(0, 0, 0, 0),
            false => Count::exact(0, 0, 1, 1),
        }
    }

    fn output_mode(input: &Self::Case) -> Mode {
        match (input.0, input.1) {
            (Mode::Constant, Mode::Constant) => Mode::Constant,
            (_, _) => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;

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
        Circuit::scope(name, || {
            let candidate = a.nor(&b);
            assert_eq!(expected, candidate.eject_value(), "({} NOR {})", a.eject_value(), b.eject_value());
            assert_scope!(num_constants, num_public, num_private, num_constraints);
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
        check_nor("false NOR false", expected, a, b, 0, 0, 1, 1);

        // false NOR true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_nor("false NOR true", expected, a, b, 0, 0, 1, 1);

        // true NOR false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Public, false);
        check_nor("true NOR false", expected, a, b, 0, 0, 1, 1);

        // true NOR true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Public, true);
        check_nor("true NOR true", expected, a, b, 0, 0, 1, 1);
    }

    #[test]
    fn test_public_nor_private() {
        // false NOR false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_nor("false NOR false", expected, a, b, 0, 0, 1, 1);

        // false NOR true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, false);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_nor("false NOR true", expected, a, b, 0, 0, 1, 1);

        // true NOR false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_nor("true NOR false", expected, a, b, 0, 0, 1, 1);

        // true NOR true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Public, true);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_nor("true NOR true", expected, a, b, 0, 0, 1, 1);
    }

    #[test]
    fn test_private_nor_private() {
        // false NOR false
        let expected = true;
        let a = Boolean::<Circuit>::new(Mode::Private, false);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_nor("false NOR false", expected, a, b, 0, 0, 1, 1);

        // false NOR true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Private, false);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_nor("false NOR true", expected, a, b, 0, 0, 1, 1);

        // true NOR false
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Private, false);
        check_nor("true NOR false", expected, a, b, 0, 0, 1, 1);

        // true NOR true
        let expected = false;
        let a = Boolean::<Circuit>::new(Mode::Private, true);
        let b = Boolean::<Circuit>::new(Mode::Private, true);
        check_nor("true NOR true", expected, a, b, 0, 0, 1, 1);
    }
}
