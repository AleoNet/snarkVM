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

impl<E: Environment> From<Field<E>> for Address<E> {
    /// Initializes an address from the **x-coordinate** of an affine group element.
    fn from(value: Field<E>) -> Self {
        Self::from_field(value)
    }
}

impl<E: Environment> From<&Field<E>> for Address<E> {
    /// Initializes an address from the **x-coordinate** of an affine group element.
    fn from(value: &Field<E>) -> Self {
        Self::from_field(value.clone())
    }
}

impl<E: Environment> FromField for Address<E> {
    type Field = Field<E>;

    /// Initializes an address from the **x-coordinate** of an affine group element.
    fn from_field(x_coordinate: Field<E>) -> Self {
        Self::from_group(Group::from_x_coordinate(x_coordinate))
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 100;

    fn check_from_field(mode: Mode, num_constants: u64, num_public: u64, num_private: u64, num_constraints: u64) {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: console::Group<<Circuit as Environment>::Network> = Uniform::rand(&mut test_rng());
            let candidate = Group::<Circuit>::new(mode, expected).to_x_coordinate();

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = Address::from_field(candidate);
                assert_eq!(expected.to_x_coordinate(), candidate.eject_value().to_x_coordinate());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
            Circuit::reset();
        }
    }

    #[test]
    fn test_from_field_constant() {
        check_from_field(Mode::Constant, 3, 0, 0, 0);
    }

    #[test]
    fn test_from_field_public() {
        check_from_field(Mode::Public, 2, 0, 3, 3);
    }

    #[test]
    fn test_from_field_private() {
        check_from_field(Mode::Private, 2, 0, 3, 3);
    }
}
