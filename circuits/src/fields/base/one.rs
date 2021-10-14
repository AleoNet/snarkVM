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

impl<E: Environment> One for BaseField<E> {
    type Boolean = Boolean<E>;
    type Output = Self::Boolean;

    fn one() -> Self {
        BaseField(E::one())
    }

    fn is_one(&self) -> Self::Output {
        self.is_eq(&BaseField::one())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;

    #[test]
    fn test_one() {
        let one = <Circuit as Environment>::BaseField::one();

        Circuit::scoped("One", |scope| {
            assert_eq!(0, Circuit::num_constants());
            assert_eq!(1, Circuit::num_public());
            assert_eq!(0, Circuit::num_private());
            assert_eq!(0, Circuit::num_constraints());

            assert_eq!(0, scope.num_constants_in_scope());
            assert_eq!(0, scope.num_public_in_scope());
            assert_eq!(0, scope.num_private_in_scope());
            assert_eq!(0, scope.num_constraints_in_scope());

            let candidate = BaseField::<Circuit>::one();
            assert_eq!(one, candidate.eject_value());

            assert_eq!(0, scope.num_constants_in_scope());
            assert_eq!(0, scope.num_public_in_scope());
            assert_eq!(0, scope.num_private_in_scope());
            assert_eq!(0, scope.num_constraints_in_scope());

            assert_eq!(0, Circuit::num_constants());
            assert_eq!(1, Circuit::num_public());
            assert_eq!(0, Circuit::num_private());
            assert_eq!(0, Circuit::num_constraints());
        });
    }

    #[test]
    fn test_is_one() {
        let candidate = BaseField::<Circuit>::one();

        // Should equal 1.
        let candidate_boolean = candidate.is_one();
        assert_eq!(true, candidate_boolean.eject_value());

        // Should not equal 0.
        let candidate_boolean = candidate.is_zero();
        assert_eq!(false, candidate_boolean.eject_value());
    }
}
