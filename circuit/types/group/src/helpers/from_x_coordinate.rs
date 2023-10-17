// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

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
        let mut rng = TestRng::default();

        for i in 0..ITERATIONS {
            // Sample a random element.
            let point: console::Group<<Circuit as Environment>::Network> = Uniform::rand(&mut rng);

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
        check_from_x_coordinate(Mode::Constant, 9, 0, 0, 0);
    }

    #[test]
    fn test_from_x_coordinate_public() {
        check_from_x_coordinate(Mode::Public, 4, 0, 13, 13);
    }

    #[test]
    fn test_from_x_coordinate_private() {
        check_from_x_coordinate(Mode::Private, 4, 0, 13, 13);
    }
}
