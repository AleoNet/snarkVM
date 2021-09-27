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

impl<E: Environment> Inv for Field<E> {
    type Output = Self;

    fn inv(self) -> Self::Output {
        (&self).inv()
    }
}

impl<E: Environment> Inv for &Field<E> {
    type Output = Field<E>;

    fn inv(self) -> Self::Output {
        let inverse = match self.to_value().inverse() {
            Some(inverse) => inverse,
            None => E::halt("Failed to compute the inverse"),
        };

        match self.0.is_constant() {
            true => Field::<E>::new(Mode::Constant, inverse),
            false => {
                let inverse = E::new_variable(Mode::Private, inverse);

                // Ensure self * self^(-1) == 1.
                E::enforce(|| (self, inverse, E::one()));

                Field(inverse.into())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;

    const ITERATIONS: usize = 100_000;

    #[test]
    fn test_inv() {
        let one = <Circuit as Environment>::Field::one();

        // Constant variables
        Circuit::scoped("Constant", |scope| {
            let mut accumulator = one;

            for i in 0..ITERATIONS {
                let expected = accumulator.inverse().unwrap();
                let candidate = Field::<Circuit>::new(Mode::Constant, accumulator).inv();
                assert_eq!(expected, candidate.to_value());

                assert_eq!((i + 1) * 2, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(0, scope.num_private_in_scope());
                assert_eq!(0, scope.num_constraints_in_scope());

                accumulator += one;
            }
        });

        // Public variables
        Circuit::scoped("Public", |scope| {
            let mut accumulator = one;

            for i in 0..ITERATIONS {
                let expected = accumulator.inverse().unwrap();
                let candidate = Field::<Circuit>::new(Mode::Public, accumulator).inv();
                assert_eq!(expected, candidate.to_value());

                assert_eq!(0, scope.num_constants_in_scope());
                assert_eq!(i + 1, scope.num_public_in_scope());
                assert_eq!(i + 1, scope.num_private_in_scope());
                assert_eq!(i + 1, scope.num_constraints_in_scope());

                accumulator += one;
            }
        });

        // Private variables
        Circuit::scoped("Private", |scope| {
            let mut accumulator = one;

            for i in 0..ITERATIONS {
                let expected = accumulator.inverse().unwrap();
                let candidate = Field::<Circuit>::new(Mode::Private, accumulator).inv();
                assert_eq!(expected, candidate.to_value());

                assert_eq!(0, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!((i + 1) * 2, scope.num_private_in_scope());
                assert_eq!(i + 1, scope.num_constraints_in_scope());

                accumulator += one;
            }
        });
    }

    #[test]
    fn test_zero_inv_fails() {
        let zero = <Circuit as Environment>::Field::zero();

        let result = std::panic::catch_unwind(|| Field::<Circuit>::zero().inv());
        assert!(result.is_err()); // Probe further for specific error type here, if desired

        let result = std::panic::catch_unwind(|| Field::<Circuit>::new(Mode::Constant, zero).inv());
        assert!(result.is_err()); // Probe further for specific error type here, if desired

        let result = std::panic::catch_unwind(|| Field::<Circuit>::new(Mode::Public, zero).inv());
        assert!(result.is_err()); // Probe further for specific error type here, if desired

        let result = std::panic::catch_unwind(|| Field::<Circuit>::new(Mode::Private, zero).inv());
        assert!(result.is_err()); // Probe further for specific error type here, if desired
    }
}
