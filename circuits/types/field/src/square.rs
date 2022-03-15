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

impl<E: Environment> Square for Field<E> {
    type Output = Field<E>;

    fn square(&self) -> Self::Output {
        (&self).square()
    }
}

impl<E: Environment> Square for &Field<E> {
    type Output = Field<E>;

    fn square(&self) -> Self::Output {
        *self * *self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 500;

    fn check_square(
        name: &str,
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for _ in 0..ITERATIONS {
            // Sample a random element.
            let given: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            let candidate = Field::<Circuit>::new(mode, given);

            Circuit::scope(name, || {
                assert_eq!(given.square(), candidate.square().eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
            Circuit::reset();
        }
    }

    #[test]
    fn test_square() {
        check_square("Constant", Mode::Constant, 0, 0, 0, 0);
        check_square("Public", Mode::Public, 0, 0, 1, 1);
        check_square("Private", Mode::Private, 0, 0, 1, 1);
    }

    #[test]
    fn test_0_square() {
        let zero = <Circuit as Environment>::BaseField::zero();

        let candidate = Field::<Circuit>::new(Mode::Public, zero).square();
        assert_eq!(zero, candidate.eject_value());
    }

    #[test]
    fn test_1_double() {
        let one = <Circuit as Environment>::BaseField::one();

        let candidate = Field::<Circuit>::new(Mode::Public, one).square();
        assert_eq!(one, candidate.eject_value());
    }

    #[test]
    fn test_2_double() {
        let one = <Circuit as Environment>::BaseField::one();
        let two = one + one;
        let four = two.square();

        let candidate = (Field::<Circuit>::new(Mode::Public, one) + Field::new(Mode::Public, one)).square();
        assert_eq!(four, candidate.eject_value());
    }
}
