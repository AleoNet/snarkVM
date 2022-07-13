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

impl<E: Environment> Zero for Group<E> {
    type Boolean = Boolean<E>;

    fn zero() -> Self {
        Group { x: Field::zero(), y: Field::one() }
    }

    fn is_zero(&self) -> Self::Boolean {
        let is_x_zero = self.x.is_equal(&Field::zero());
        let is_y_one = self.y.is_equal(&Field::one());
        is_x_zero & is_y_one
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    #[test]
    fn test_zero() {
        let zero = console::Field::zero();
        let one = console::Field::one();

        Circuit::scope("Zero", || {
            assert_scope!(0, 0, 0, 0);
            let candidate = Group::<Circuit>::zero().eject_value();
            assert_eq!(zero, candidate.to_x_coordinate());
            assert_eq!(one, candidate.to_y_coordinate());
            assert_scope!(0, 0, 0, 0);
        });
    }

    #[test]
    fn test_is_zero() {
        let candidate = Group::<Circuit>::zero();
        // Should equal 0.
        assert!(candidate.is_zero().eject_value());
    }
}
