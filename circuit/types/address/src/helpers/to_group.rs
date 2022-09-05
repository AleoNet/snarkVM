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

impl<E: Environment> From<Address<E>> for Group<E> {
    /// Returns the affine group element in the address.
    fn from(value: Address<E>) -> Self {
        value.to_group()
    }
}

impl<E: Environment> From<&Address<E>> for Group<E> {
    /// Returns the affine group element in the address.
    fn from(value: &Address<E>) -> Self {
        value.to_group()
    }
}

impl<E: Environment> ToGroup for Address<E> {
    type Group = Group<E>;
    type Scalar = Scalar<E>;

    /// Returns the affine group element in the address.
    fn to_group(&self) -> Self::Group {
        self.0.clone()
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    fn check_to_group(
        name: &str,
        expected: console::Group<<Circuit as Environment>::Network>,
        candidate: &Address<Circuit>,
    ) {
        Circuit::scope(name, || {
            // Perform the operation.
            let candidate = candidate.to_group();
            assert_eq!(expected, candidate.eject_value());
            assert_scope!(0, 0, 0, 0);
        });
    }

    #[test]
    fn test_to_group_constant() {
        let expected = console::Address::new(Uniform::rand(&mut test_rng()));
        let candidate = Address::<Circuit>::new(Mode::Constant, expected);
        check_to_group("Constant", *expected, &candidate);
    }

    #[test]
    fn test_to_group_public() {
        let expected = console::Address::new(Uniform::rand(&mut test_rng()));
        let candidate = Address::<Circuit>::new(Mode::Public, expected);
        check_to_group("Public", *expected, &candidate);
    }

    #[test]
    fn test_to_group_private() {
        let expected = console::Address::new(Uniform::rand(&mut test_rng()));
        let candidate = Address::<Circuit>::new(Mode::Private, expected);
        check_to_group("Private", *expected, &candidate);
    }
}
