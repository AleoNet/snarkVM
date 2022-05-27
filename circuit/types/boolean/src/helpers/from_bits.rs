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

impl<E: Environment> FromBits for Boolean<E> {
    type Boolean = Boolean<E>;

    /// Returns a boolean circuit given a mode and single boolean.
    fn from_bits_le(bits_le: &[Self::Boolean]) -> Self {
        // Ensure there is exactly one boolean in the list of booleans.
        match bits_le.len() == 1 {
            true => bits_le[0].clone(),
            false => E::halt(format!("Attempted to instantiate a boolean with {} bits", bits_le.len())),
        }
    }

    /// Returns a boolean circuit given a mode and single boolean.
    fn from_bits_be(bits_be: &[Self::Boolean]) -> Self {
        // Ensure there is exactly one boolean in the list of booleans.
        match bits_be.len() == 1 {
            true => bits_be[0].clone(),
            false => E::halt(format!("Attempted to instantiate a boolean with {} bits", bits_be.len())),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    fn check_from_bits_le(
        name: &str,
        expected: bool,
        candidate: &Boolean<Circuit>,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        Circuit::scope(name, || {
            let candidate = Boolean::from_bits_le(&[(*candidate).clone()]);
            assert_eq!(expected, candidate.eject_value());
            assert_scope!(num_constants, num_public, num_private, num_constraints);
        });
        Circuit::reset();
    }

    fn check_from_bits_be(
        name: &str,
        expected: bool,
        candidate: &Boolean<Circuit>,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        Circuit::scope(name, || {
            let candidate = Boolean::from_bits_be(&[(*candidate).clone()]);
            assert_eq!(expected, candidate.eject_value());
            assert_scope!(num_constants, num_public, num_private, num_constraints);
        });
        Circuit::reset();
    }

    #[test]
    fn test_from_bits_constant() {
        let candidate = Boolean::<Circuit>::new(Mode::Constant, true);
        check_from_bits_le("Constant", true, &candidate, 0, 0, 0, 0);
        check_from_bits_be("Constant", true, &candidate, 0, 0, 0, 0);

        let candidate = Boolean::<Circuit>::new(Mode::Constant, false);
        check_from_bits_le("Constant", false, &candidate, 0, 0, 0, 0);
        check_from_bits_be("Constant", false, &candidate, 0, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_public() {
        let candidate = Boolean::<Circuit>::new(Mode::Public, true);
        check_from_bits_le("Public", true, &candidate, 0, 0, 0, 0);
        check_from_bits_be("Public", true, &candidate, 0, 0, 0, 0);

        let candidate = Boolean::<Circuit>::new(Mode::Public, false);
        check_from_bits_le("Public", false, &candidate, 0, 0, 0, 0);
        check_from_bits_be("Public", false, &candidate, 0, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_private() {
        let candidate = Boolean::<Circuit>::new(Mode::Private, true);
        check_from_bits_le("Private", true, &candidate, 0, 0, 0, 0);
        check_from_bits_be("Private", true, &candidate, 0, 0, 0, 0);

        let candidate = Boolean::<Circuit>::new(Mode::Private, false);
        check_from_bits_le("Private", false, &candidate, 0, 0, 0, 0);
        check_from_bits_be("Private", false, &candidate, 0, 0, 0, 0);
    }
}
