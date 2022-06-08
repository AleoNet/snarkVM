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
    /// Initializes an affine group element from a given x-coordinate field element.
    /// For safety, the resulting point is always enforced to be on the curve with constraints.
    pub fn from_x_coordinate(x: Field<E>) -> Self {
        // Derive the y-coordinate.
        let y = witness!(|x| match console::Group::from_x_coordinate(x) {
            Ok(point) => point.to_y_coordinate(),
            Err(_) => console::Field::zero(),
        });

        Self::from_xy_coordinates(x, y)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 100;

    fn check_from_x_coordinate(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: console::Group<<Circuit as Environment>::Network> = Uniform::rand(&mut test_rng());

            // Inject the x-coordinate.
            let x_coordinate = Field::new(mode, point.to_x_coordinate());

            Circuit::scope(format!("{mode} {i}"), || {
                let affine = Group::<Circuit>::from_x_coordinate(x_coordinate);
                assert_eq!(point, affine.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
            Circuit::reset();
        }
    }

    #[test]
    fn test_from_x_coordinate_constant() {
        check_from_x_coordinate(Mode::Constant, 3, 0, 0, 0);
    }

    #[test]
    fn test_from_x_coordinate_public() {
        check_from_x_coordinate(Mode::Public, 2, 0, 3, 3);
    }

    #[test]
    fn test_from_x_coordinate_private() {
        check_from_x_coordinate(Mode::Private, 2, 0, 3, 3);
    }
}
