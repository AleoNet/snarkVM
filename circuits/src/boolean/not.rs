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

    fn not(self) -> Self::Output {
        (&self).not()
    }
}

impl<E: Environment> Not for &Boolean<E> {
    type Output = Boolean<E>;

    fn not(self) -> Self::Output {
        // Perform a software-level safety check that the boolean is well-formed.
        if !self.0.is_boolean_type() {
            E::halt("Boolean variable is not well-formed")
        }

        let one = E::BaseField::one();
        let boolean = self.to_value();

        let output = if self.0.is_constant() {
            // Constant case
            match boolean {
                true => self.0.clone() - Variable::Constant(one),
                false => self.0.clone() + Variable::Constant(one),
            }
        } else {
            // Public and private cases
            match boolean {
                true => self.0.clone() - E::one(),
                false => self.0.clone() + E::one(),
            }
        };

        Boolean(output)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;

    #[test]
    fn test_not() {
        assert_eq!(0, Circuit::num_constants());
        assert_eq!(1, Circuit::num_public());
        assert_eq!(0, Circuit::num_private());
        assert_eq!(0, Circuit::num_constraints());

        let candidate = !Boolean::<Circuit>::new(Mode::Constant, false);
        assert_eq!(true, candidate.to_value());
        assert!(Circuit::is_satisfied());

        let candidate = !Boolean::<Circuit>::new(Mode::Constant, true);
        assert_eq!(false, candidate.to_value());
        assert!(Circuit::is_satisfied());

        assert_eq!(2, Circuit::num_constants());
        assert_eq!(1, Circuit::num_public());
        assert_eq!(0, Circuit::num_private());
        assert_eq!(0, Circuit::num_constraints());

        let candidate = !Boolean::<Circuit>::new(Mode::Public, false);
        assert_eq!(true, candidate.to_value());
        assert!(Circuit::is_satisfied());

        assert_eq!(2, Circuit::num_constants());
        assert_eq!(2, Circuit::num_public());
        assert_eq!(0, Circuit::num_private());
        assert_eq!(1, Circuit::num_constraints());

        let candidate = !Boolean::<Circuit>::new(Mode::Public, true);
        assert_eq!(false, candidate.to_value());
        assert!(Circuit::is_satisfied());

        let candidate = !Boolean::<Circuit>::new(Mode::Private, false);
        assert_eq!(true, candidate.to_value());
        assert!(Circuit::is_satisfied());

        let candidate = !Boolean::<Circuit>::new(Mode::Private, true);
        assert_eq!(false, candidate.to_value());
        assert!(Circuit::is_satisfied());
    }
}
