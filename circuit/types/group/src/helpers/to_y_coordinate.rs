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
    /// Returns the y-coordinate of the group element.
    pub fn to_y_coordinate(&self) -> Field<E> {
        self.y.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 100;

    fn check_to_y_coordinate(mode: Mode) {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected = Uniform::rand(&mut test_rng());
            let candidate = Group::<Circuit>::new(mode, expected);

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = candidate.to_y_coordinate();
                assert_eq!(expected.to_y_coordinate(), candidate.eject_value());
                assert_scope!(0, 0, 0, 0);
            });
        }
    }

    #[test]
    fn test_to_y_coordinate_constant() {
        check_to_y_coordinate(Mode::Constant);
    }

    #[test]
    fn test_to_y_coordinate_public() {
        check_to_y_coordinate(Mode::Public);
    }

    #[test]
    fn test_to_y_coordinate_private() {
        check_to_y_coordinate(Mode::Private);
    }
}
