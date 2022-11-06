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

impl<E: Environment> Group<E> {
    /// Initializes an affine group element from a given x- and y-coordinate field element.
    /// For safety, the resulting point is always enforced to be on the curve and in the subgroup.
    pub fn from_xy_coordinates(x: Field<E>, y: Field<E>) -> Self {
        // Recover point from the `(x, y)` coordinates as a witness.
        witness!(|x, y| console::Group::from_xy_coordinates(x, y))
    }

    /// Initializes an affine group element from a given x- and y-coordinate field element.
    /// Note: The resulting point is **not** enforced to be on the curve or in the subgroup.
    #[doc(hidden)]
    pub fn from_xy_coordinates_unchecked(x: Field<E>, y: Field<E>) -> Self {
        Self { x, y }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 100;

    fn check_from_xy_coordinates(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        let mut rng = TestRng::default();

        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: console::Group<<Circuit as Environment>::Network> = Uniform::rand(&mut rng);

            // Inject the x- and y-coordinates.
            let x_coordinate = Field::new(mode, point.to_x_coordinate());
            let y_coordinate = Field::new(mode, point.to_y_coordinate());

            Circuit::scope(format!("{mode} {i}"), || {
                let affine = Group::<Circuit>::from_xy_coordinates(x_coordinate, y_coordinate);
                assert_eq!(point, affine.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    fn check_from_xy_coordinates_unchecked(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        let mut rng = TestRng::default();

        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: console::Group<<Circuit as Environment>::Network> = Uniform::rand(&mut rng);

            // Inject the x- and y-coordinates.
            let x_coordinate = Field::new(mode, point.to_x_coordinate());
            let y_coordinate = Field::new(mode, point.to_y_coordinate());

            Circuit::scope(format!("{mode} {i}"), || {
                let affine = Group::<Circuit>::from_xy_coordinates_unchecked(x_coordinate, y_coordinate);
                assert_eq!(point, affine.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    #[test]
    fn test_from_xy_coordinates_constant() {
        check_from_xy_coordinates(Mode::Constant, 10, 0, 0, 0);
    }

    #[test]
    fn test_from_xy_coordinates_public() {
        check_from_xy_coordinates(Mode::Public, 4, 0, 14, 13);
    }

    #[test]
    fn test_from_xy_coordinates_private() {
        check_from_xy_coordinates(Mode::Private, 4, 0, 14, 13);
    }

    #[test]
    fn test_from_xy_coordinates_unchecked_constant() {
        check_from_xy_coordinates_unchecked(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_from_xy_coordinates_unchecked_public() {
        check_from_xy_coordinates_unchecked(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_from_xy_coordinates_unchecked_private() {
        check_from_xy_coordinates_unchecked(Mode::Private, 0, 0, 0, 0);
    }
}
