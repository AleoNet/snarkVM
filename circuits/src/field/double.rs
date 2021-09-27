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

impl<E: Environment> Double for Field<E> {
    type Output = Field<E>;

    fn double(self) -> Self::Output {
        (&self).double()
    }
}

impl<E: Environment> Double for &Field<E> {
    type Output = Field<E>;

    fn double(self) -> Self::Output {
        Field(&self.0 + &self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;

    const ITERATIONS: usize = 10_000;

    #[test]
    fn test_double() {
        let one = <Circuit as Environment>::BaseField::one();

        // Constant variables
        Circuit::scoped("Constant", |scope| {
            let mut expected = one;
            let mut candidate = Field::<Circuit>::new(Mode::Constant, one);

            for _ in 0..ITERATIONS {
                expected = expected.double();
                candidate = candidate.double();
                assert_eq!(expected, candidate.to_value());

                assert_eq!(1, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(0, scope.num_private_in_scope());
                assert_eq!(0, scope.num_constraints_in_scope());
            }
        });

        // Public variables
        Circuit::scoped("Public", |scope| {
            let mut expected = one;
            let mut candidate = Field::<Circuit>::new(Mode::Public, one);

            for _ in 0..ITERATIONS {
                expected = expected.double();
                candidate = candidate.double();
                assert_eq!(expected, candidate.to_value());

                assert_eq!(0, scope.num_constants_in_scope());
                assert_eq!(1, scope.num_public_in_scope());
                assert_eq!(0, scope.num_private_in_scope());
                assert_eq!(0, scope.num_constraints_in_scope());
            }
        });

        // Private variables
        Circuit::scoped("Private", |scope| {
            let mut expected = one;
            let mut candidate = Field::<Circuit>::new(Mode::Private, one);

            for _ in 0..ITERATIONS {
                expected = expected.double();
                candidate = candidate.double();
                assert_eq!(expected, candidate.to_value());

                assert_eq!(0, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(1, scope.num_private_in_scope());
                assert_eq!(0, scope.num_constraints_in_scope());
            }
        });
    }

    #[test]
    fn test_0_double() {
        let zero = <Circuit as Environment>::BaseField::zero();

        let candidate = Field::<Circuit>::new(Mode::Public, zero).double();
        assert_eq!(zero, candidate.to_value());
    }

    #[test]
    fn test_1_double() {
        let one = <Circuit as Environment>::BaseField::one();
        let two = one + one;

        let candidate = Field::<Circuit>::new(Mode::Public, one).double();
        assert_eq!(two, candidate.to_value());
    }
}
