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
use snarkvm_circuits_field::BaseField;

impl<E: Environment> ToField for Boolean<E> {
    type Boolean = Self;
    type Field = BaseField<E>;

    /// Casts a boolean into a base field element.
    fn to_field(&self) -> Self::Field {
        BaseField::from(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;

    fn check_to_field(name: &str, expected: bool, candidate: &Boolean<Circuit>) {
        Circuit::scope(name, || {
            // Perform the operation.
            let candidate = candidate.to_field();
            assert_scope!(0, 0, 0, 0);

            match expected {
                true => assert_eq!(<Circuit as Environment>::BaseField::one(), candidate.eject_value()),
                false => assert_eq!(<Circuit as Environment>::BaseField::zero(), candidate.eject_value()),
            }
        });
        Circuit::reset();
    }

    #[test]
    fn test_to_field_constant() {
        let candidate = Boolean::<Circuit>::new(Mode::Constant, true);
        check_to_field("Constant", true, &candidate);

        let candidate = Boolean::<Circuit>::new(Mode::Constant, false);
        check_to_field("Constant", false, &candidate);
    }

    #[test]
    fn test_to_field_public() {
        let candidate = Boolean::<Circuit>::new(Mode::Public, true);
        check_to_field("Public", true, &candidate);

        let candidate = Boolean::<Circuit>::new(Mode::Public, false);
        check_to_field("Public", false, &candidate);
    }

    #[test]
    fn test_to_field_private() {
        let candidate = Boolean::<Circuit>::new(Mode::Private, true);
        check_to_field("Private", true, &candidate);

        let candidate = Boolean::<Circuit>::new(Mode::Private, false);
        check_to_field("Private", false, &candidate);
    }
}
