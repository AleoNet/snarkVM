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

impl<E: Environment> From<Group<E>> for Address<E> {
    /// Initializes an address from an affine group element.
    fn from(value: Group<E>) -> Self {
        Self::from_group(value)
    }
}

impl<E: Environment> From<&Group<E>> for Address<E> {
    /// Initializes an address from an affine group element.
    fn from(value: &Group<E>) -> Self {
        Self::from_group(value.clone())
    }
}

impl<E: Environment> FromGroup for Address<E> {
    type Group = Group<E>;
    type Scalar = Scalar<E>;

    /// Initializes an address from an affine group element.
    fn from_group(group: Self::Group) -> Self {
        Self(group)
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    fn check_from_group(
        name: &str,
        expected: console::Address<<Circuit as Environment>::Network>,
        candidate: &Group<Circuit>,
    ) {
        Circuit::scope(name, || {
            // Perform the operation.
            let candidate = Address::from_group(candidate.clone());
            assert_eq!(expected, candidate.eject_value());
            assert_scope!(0, 0, 0, 0);
        });
    }

    #[test]
    fn test_from_group_constant() {
        let expected = console::Address::new(Uniform::rand(&mut test_rng()));
        let candidate = Group::<Circuit>::new(Mode::Constant, *expected);
        check_from_group("Constant", expected, &candidate);
    }

    #[test]
    fn test_from_group_public() {
        let expected = console::Address::new(Uniform::rand(&mut test_rng()));
        let candidate = Group::<Circuit>::new(Mode::Public, *expected);
        check_from_group("Public", expected, &candidate);
    }

    #[test]
    fn test_from_group_private() {
        let expected = console::Address::new(Uniform::rand(&mut test_rng()));
        let candidate = Group::<Circuit>::new(Mode::Private, *expected);
        check_from_group("Private", expected, &candidate);
    }
}
