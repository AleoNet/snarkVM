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

impl<E: Environment> Not for Boolean<E> {
    type Output = Boolean<E>;

    /// Returns `(NOT a)`.
    fn not(self) -> Self::Output {
        (&self).not()
    }
}

impl<E: Environment> Not for &Boolean<E> {
    type Output = Boolean<E>;

    /// Returns `(NOT a)`.
    fn not(self) -> Self::Output {
        // Perform a software-level safety check that the boolean is well-formed.
        if !self.0.is_boolean_type() {
            E::halt("Boolean variable is not well-formed")
        }

        // Constant case
        if self.is_constant() {
            match self.to_value() {
                true => Boolean(self.0.clone() - Variable::one()),
                false => Boolean(self.0.clone() + Variable::one()),
            }
        }
        // Public and private cases
        else {
            match self.to_value() {
                true => Boolean(self.0.clone() - Variable::Public(0, E::BaseField::one())),
                false => Boolean(self.0.clone() + Variable::Public(0, E::BaseField::one())),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;

    fn check_not(
        name: &str,
        expected: bool,
        candidate_input: Boolean<Circuit>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, |scope| {
            let candidate_output = !candidate_input;
            assert_eq!(expected, candidate_output.to_value());

            assert_eq!(num_constants, scope.num_constants_in_scope());
            assert_eq!(num_public, scope.num_public_in_scope());
            assert_eq!(num_private, scope.num_private_in_scope());
            assert_eq!(num_constraints, scope.num_constraints_in_scope());
            assert!(Circuit::is_satisfied());
        });
    }

    #[test]
    fn test_not_constant() {
        // NOT false
        let expected = true;
        let candidate_input = Boolean::<Circuit>::new(Mode::Constant, false);
        check_not("NOT false", expected, candidate_input, 0, 0, 0, 0);

        // NOT true
        let expected = false;
        let candidate_input = Boolean::<Circuit>::new(Mode::Constant, true);
        check_not("NOT true", expected, candidate_input, 0, 0, 0, 0);
    }

    #[test]
    fn test_not_public() {
        // NOT false
        let expected = true;
        let candidate_input = Boolean::<Circuit>::new(Mode::Public, false);
        check_not("NOT false", expected, candidate_input, 0, 0, 0, 0);

        // NOT true
        let expected = false;
        let candidate_input = Boolean::<Circuit>::new(Mode::Public, true);
        check_not("NOT true", expected, candidate_input, 0, 0, 0, 0);
    }

    #[test]
    fn test_not_private() {
        // NOT false
        let expected = true;
        let candidate_input = Boolean::<Circuit>::new(Mode::Private, false);
        check_not("NOT false", expected, candidate_input, 0, 0, 0, 0);

        // NOT true
        let expected = false;
        let candidate_input = Boolean::<Circuit>::new(Mode::Private, true);
        check_not("NOT true", expected, candidate_input, 0, 0, 0, 0);
    }
}
