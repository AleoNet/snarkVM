// Copyright (C) 2019-2021 Aleo Systems Inc.
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

impl<E: Environment> Double for BaseField<E> {
    type Output = BaseField<E>;

    fn double(self) -> Self::Output {
        (&self).double()
    }
}

impl<E: Environment> Double for &BaseField<E> {
    type Output = BaseField<E>;

    fn double(self) -> Self::Output {
        BaseField(&self.0 + &self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;

    const ITERATIONS: usize = 10_000;

    #[test]
    fn test_double() {
        let one = <Circuit as Environment>::BaseField::one();

        // Constant variables
        Circuit::scoped("Constant", || {
            let mut expected = one;
            let mut candidate = BaseField::<Circuit>::new(Mode::Constant, one);

            for _ in 0..ITERATIONS {
                expected = expected.double();
                candidate = candidate.double();
                assert_eq!(expected, candidate.eject_value());

                assert_eq!(1, Circuit::num_constants_in_scope());
                assert_eq!(0, Circuit::num_public_in_scope());
                assert_eq!(0, Circuit::num_private_in_scope());
                assert_eq!(0, Circuit::num_constraints_in_scope());
            }
        });

        // Public variables
        Circuit::scoped("Public", || {
            let mut expected = one;
            let mut candidate = BaseField::<Circuit>::new(Mode::Public, one);

            for _ in 0..ITERATIONS {
                expected = expected.double();
                candidate = candidate.double();
                assert_eq!(expected, candidate.eject_value());

                assert_eq!(0, Circuit::num_constants_in_scope());
                assert_eq!(1, Circuit::num_public_in_scope());
                assert_eq!(0, Circuit::num_private_in_scope());
                assert_eq!(0, Circuit::num_constraints_in_scope());
            }
        });

        // Private variables
        Circuit::scoped("Private", || {
            let mut expected = one;
            let mut candidate = BaseField::<Circuit>::new(Mode::Private, one);

            for _ in 0..ITERATIONS {
                expected = expected.double();
                candidate = candidate.double();
                assert_eq!(expected, candidate.eject_value());

                assert_eq!(0, Circuit::num_constants_in_scope());
                assert_eq!(0, Circuit::num_public_in_scope());
                assert_eq!(1, Circuit::num_private_in_scope());
                assert_eq!(0, Circuit::num_constraints_in_scope());
            }
        });
    }

    #[test]
    fn test_0_double() {
        let zero = <Circuit as Environment>::BaseField::zero();

        let candidate = BaseField::<Circuit>::new(Mode::Public, zero).double();
        assert_eq!(zero, candidate.eject_value());
    }

    #[test]
    fn test_1_double() {
        let one = <Circuit as Environment>::BaseField::one();
        let two = one + one;

        let candidate = BaseField::<Circuit>::new(Mode::Public, one).double();
        assert_eq!(two, candidate.eject_value());
    }
}
