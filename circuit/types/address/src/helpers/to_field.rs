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

impl<E: Environment> From<Address<E>> for Field<E> {
    /// Returns the **x-coordinate** of the affine group element in the address.
    fn from(value: Address<E>) -> Self {
        value.to_field()
    }
}

impl<E: Environment> From<&Address<E>> for Field<E> {
    /// Returns the **x-coordinate** of the affine group element in the address.
    fn from(value: &Address<E>) -> Self {
        value.to_field()
    }
}

impl<E: Environment> ToField for Address<E> {
    type Field = Field<E>;

    /// Returns the **x-coordinate** of the affine group element in the address.
    fn to_field(&self) -> Field<E> {
        self.0.to_x_coordinate()
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 100;

    fn check_to_field(mode: Mode) {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected = Uniform::rand(&mut test_rng());
            let candidate = Address::<Circuit>::from_group(Group::new(mode, expected));

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = candidate.to_field();
                assert_eq!(expected.to_x_coordinate(), candidate.eject_value());
                assert_scope!(0, 0, 0, 0);
            });
        }
    }

    #[test]
    fn test_to_field_constant() {
        check_to_field(Mode::Constant);
    }

    #[test]
    fn test_to_field_public() {
        check_to_field(Mode::Public);
    }

    #[test]
    fn test_to_field_private() {
        check_to_field(Mode::Private);
    }
}
