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

impl<E: Environment> FromBoolean for Field<E> {
    type Boolean = Boolean<E>;

    /// Initializes a base field from a boolean.
    fn from_boolean(boolean: &Self::Boolean) -> Self {
        (&**boolean).into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;

    fn check_from_boolean(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for expected in &[true, false] {
            // Inject the boolean.
            let given = Boolean::<Circuit>::new(mode, *expected);

            Circuit::scope(format!("{mode} {expected}"), || {
                let candidate = Field::from_boolean(&given);
                match expected {
                    true => assert_eq!(<Circuit as Environment>::BaseField::one(), candidate.eject_value()),
                    false => assert_eq!(<Circuit as Environment>::BaseField::zero(), candidate.eject_value()),
                }
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    #[test]
    fn test_from_boolean_constant() {
        check_from_boolean(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_from_boolean_public() {
        check_from_boolean(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_from_boolean_private() {
        check_from_boolean(Mode::Private, 0, 0, 0, 0);
    }
}
