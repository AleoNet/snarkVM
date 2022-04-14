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

impl<E: Environment> Count<dyn Not<Output = Boolean<E>>> for Boolean<E> {
    type Case = Mode;

    fn count(_input: &Self::Case) -> CircuitCount {
        CircuitCount::exact(0, 0, 0, 0)
    }
}

impl<E: Environment> OutputMode<dyn Not<Output = Boolean<E>>> for Boolean<E> {
    type Case = Mode;

    fn output_mode(input: &Self::Case) -> Mode {
        match input {
            Mode::Constant => Mode::Constant,
            _ => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;

    fn check_not(name: &str, expected: bool, candidate_input: Boolean<Circuit>) {
        Circuit::scope(name, || {
            let mode = candidate_input.mode();
            let candidate_output = !candidate_input;
            assert_eq!(expected, candidate_output.eject_value());
            assert_count!(Boolean<Circuit>, Not<Output = Boolean<Circuit>>, &mode);
            assert_output_mode!(
                candidate_output,
                Boolean<Circuit>,
                Not<Output = Boolean<Circuit>>,
                &mode
            );
        });
    }

    #[test]
    fn test_not_constant() {
        // NOT false
        let expected = true;
        let candidate_input = Boolean::<Circuit>::new(Mode::Constant, false);
        check_not("NOT false", expected, candidate_input);

        // NOT true
        let expected = false;
        let candidate_input = Boolean::<Circuit>::new(Mode::Constant, true);
        check_not("NOT true", expected, candidate_input);
    }

    #[test]
    fn test_not_public() {
        // NOT false
        let expected = true;
        let candidate_input = Boolean::<Circuit>::new(Mode::Public, false);
        check_not("NOT false", expected, candidate_input);

        // NOT true
        let expected = false;
        let candidate_input = Boolean::<Circuit>::new(Mode::Public, true);
        check_not("NOT true", expected, candidate_input);
    }

    #[test]
    fn test_not_private() {
        // NOT false
        let expected = true;
        let candidate_input = Boolean::<Circuit>::new(Mode::Private, false);
        check_not("NOT false", expected, candidate_input);

        // NOT true
        let expected = false;
        let candidate_input = Boolean::<Circuit>::new(Mode::Private, true);
        check_not("NOT true", expected, candidate_input);
    }
}
