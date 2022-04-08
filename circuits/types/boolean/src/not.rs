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
use std::rc::Rc;

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
        // Constant case
        if self.is_constant() {
            match self.eject_value() {
                true => Boolean(&self.0 - E::one()),
                false => Boolean(&self.0 + E::one()),
            }
        }
        // Public and private cases
        else {
            match self.eject_value() {
                true => Boolean(&self.0 - Variable::Public(0, Rc::new(E::BaseField::one()))),
                false => Boolean(&self.0 + Variable::Public(0, Rc::new(E::BaseField::one()))),
            }
        }
    }
}

impl<E: Environment> MetadataForOp<dyn Not<Output = Boolean<E>>> for Boolean<E> {
    type Case = Mode;

    fn count(input: &Self::Case) -> Count {
        match input.is_constant() {
            true => Count::exact(0, 0, 0, 0),
            false => Count::exact(0, 0, 1, 1),
        }
    }

    fn output_mode(input: &Self::Case) -> Mode {
        *input
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;

    fn check_not(
        name: &str,
        expected: bool,
        candidate_input: Boolean<Circuit>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scope(name, || {
            let candidate_output = !candidate_input;
            assert_eq!(expected, candidate_output.eject_value());
            assert_scope!(num_constants, num_public, num_private, num_constraints);
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
