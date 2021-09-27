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
        let inverse = self.to_value().inverse().expect("Failed to compute the inverse");
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
    use crate::CircuitBuilder;

    const ITERATIONS: usize = 500_000;

    #[test]
    fn test_inv() {
        // let zero = <CircuitBuilder as Environment>::Field::zero();
        let one = <CircuitBuilder as Environment>::Field::one();

        // Constant variables
        CircuitBuilder::scoped("Constant", |scope| {
            let mut accumulator = one;

            for i in 0..ITERATIONS {
                let expected = accumulator.inverse().unwrap();
                let candidate = Field::<CircuitBuilder>::new(Mode::Constant, accumulator).inv();
                assert_eq!(expected, candidate.to_value());

                assert_eq!((i + 1) * 2, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(0, scope.num_private_in_scope());
                assert_eq!(0, scope.num_constraints_in_scope());

                accumulator += one;
            }
        });

        // Public variables
        CircuitBuilder::scoped("Public", |scope| {
            let mut accumulator = one;

            for i in 0..ITERATIONS {
                let expected = accumulator.inverse().unwrap();
                let candidate = Field::<CircuitBuilder>::new(Mode::Public, accumulator).inv();
                assert_eq!(expected, candidate.to_value());

                assert_eq!(0, scope.num_constants_in_scope());
                assert_eq!(i + 1, scope.num_public_in_scope());
                assert_eq!(i + 1, scope.num_private_in_scope());
                assert_eq!(i + 1, scope.num_constraints_in_scope());

                accumulator += one;
            }
        });

        // Private variables
        CircuitBuilder::scoped("Private", |scope| {
            let mut accumulator = one;

            for i in 0..ITERATIONS {
                let expected = accumulator.inverse().unwrap();
                let candidate = Field::<CircuitBuilder>::new(Mode::Private, accumulator).inv();
                assert_eq!(expected, candidate.to_value());

                assert_eq!(0, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!((i + 1) * 2, scope.num_private_in_scope());
                assert_eq!(i + 1, scope.num_constraints_in_scope());

                accumulator += one;
            }
        });
    }
}
