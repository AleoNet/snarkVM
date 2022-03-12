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
    fn from_bits_le(mode: Mode, bits_le: &[Self::Boolean]) -> Self {
        // Ensure there is exactly one boolean in the list of booleans.
        let candidate = match bits_le.len() == 1 {
            true => bits_le[0].clone(),
            false => E::halt(format!("Attempted to instantiate a boolean with {} bits", bits_le.len())),
        };

        // Ensure the mode in the given bit is consistent with the desired mode.
        // If they do not match, proceed to construct a new boolean, and check that it is well-formed.
        match candidate.eject_mode() == mode {
            true => candidate,
            false => {
                // Construct a new boolean as a witness.
                let output = Boolean(
                    E::new_variable(mode, match candidate.eject_value() {
                        true => E::BaseField::one(),
                        false => E::BaseField::zero(),
                    })
                    .into(),
                );
                // Ensure `output` == `candidate`.
                E::assert_eq(&output, &candidate);
                // Return the new boolean.
                output
            }
        }
    }

    /// Returns a boolean circuit given a mode and single boolean.
    fn from_bits_be(mode: Mode, bits_be: &[Self::Boolean]) -> Self {
        // Ensure there is exactly one boolean in the list of booleans.
        let candidate = match bits_be.len() == 1 {
            true => bits_be[0].clone(),
            false => E::halt(format!("Attempted to instantiate a boolean with {} bits", bits_be.len())),
        };

        // Ensure the mode in the given bit is consistent with the desired mode.
        // If they do not match, proceed to construct a new boolean, and check that it is well-formed.
        match candidate.eject_mode() == mode {
            true => candidate,
            false => {
                // Construct a new boolean as a witness.
                let output = Boolean(
                    E::new_variable(mode, match candidate.eject_value() {
                        true => E::BaseField::one(),
                        false => E::BaseField::zero(),
                    })
                    .into(),
                );
                // Ensure `output` == `candidate`.
                E::assert_eq(&output, &candidate);
                // Return the new boolean.
                output
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_circuit, Circuit};

    fn check_from_bits_le(
        name: &str,
        expected: bool,
        mode: Mode,
        candidate: &Boolean<Circuit>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, || {
            let candidate = Boolean::from_bits_le(mode, &[(*candidate).clone()]);
            assert_eq!(expected, candidate.eject_value());
            assert_circuit!(num_constants, num_public, num_private, num_constraints);
        });
        Circuit::reset();
    }

    fn check_from_bits_be(
        name: &str,
        expected: bool,
        mode: Mode,
        candidate: &Boolean<Circuit>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, || {
            let candidate = Boolean::from_bits_be(mode, &[(*candidate).clone()]);
            assert_eq!(expected, candidate.eject_value());
            assert_circuit!(num_constants, num_public, num_private, num_constraints);
        });
        Circuit::reset();
    }

    #[test]
    fn test_from_bits_constant() {
        let candidate = Boolean::<Circuit>::new(Mode::Constant, true);
        check_from_bits_le("Constant", true, Mode::Constant, &candidate, 0, 0, 0, 0);
        check_from_bits_be("Constant", true, Mode::Constant, &candidate, 0, 0, 0, 0);

        // Check that casting produces the correct constraints.
        {
            check_from_bits_le("Public", true, Mode::Public, &candidate, 0, 1, 0, 1);
            check_from_bits_be("Public", true, Mode::Public, &candidate, 0, 1, 0, 1);

            check_from_bits_le("Private", true, Mode::Private, &candidate, 0, 0, 1, 1);
            check_from_bits_be("Private", true, Mode::Private, &candidate, 0, 0, 1, 1);
        }

        let candidate = Boolean::<Circuit>::new(Mode::Constant, false);
        check_from_bits_le("Constant", false, Mode::Constant, &candidate, 0, 0, 0, 0);
        check_from_bits_be("Constant", false, Mode::Constant, &candidate, 0, 0, 0, 0);

        // Check that casting produces the correct constraints.
        {
            check_from_bits_le("Public", false, Mode::Public, &candidate, 0, 1, 0, 1);
            check_from_bits_be("Public", false, Mode::Public, &candidate, 0, 1, 0, 1);

            check_from_bits_le("Private", false, Mode::Private, &candidate, 0, 0, 1, 1);
            check_from_bits_be("Private", false, Mode::Private, &candidate, 0, 0, 1, 1);
        }
    }

    #[test]
    fn test_from_bits_public() {
        let candidate = Boolean::<Circuit>::new(Mode::Public, true);
        check_from_bits_le("Public", true, Mode::Public, &candidate, 0, 0, 0, 0);
        check_from_bits_be("Public", true, Mode::Public, &candidate, 0, 0, 0, 0);

        // Check that casting produces the correct constraints.
        {
            check_from_bits_le("Constant", true, Mode::Constant, &candidate, 1, 0, 0, 1);
            check_from_bits_be("Constant", true, Mode::Constant, &candidate, 1, 0, 0, 1);

            check_from_bits_le("Private", true, Mode::Private, &candidate, 0, 0, 1, 1);
            check_from_bits_be("Private", true, Mode::Private, &candidate, 0, 0, 1, 1);
        }

        let candidate = Boolean::<Circuit>::new(Mode::Public, false);
        check_from_bits_le("Public", false, Mode::Public, &candidate, 0, 0, 0, 0);
        check_from_bits_be("Public", false, Mode::Public, &candidate, 0, 0, 0, 0);

        // Check that casting produces the correct constraints.
        {
            check_from_bits_le("Constant", false, Mode::Constant, &candidate, 1, 0, 0, 1);
            check_from_bits_be("Constant", false, Mode::Constant, &candidate, 1, 0, 0, 1);

            check_from_bits_le("Private", false, Mode::Private, &candidate, 0, 0, 1, 1);
            check_from_bits_be("Private", false, Mode::Private, &candidate, 0, 0, 1, 1);
        }
    }

    #[test]
    fn test_from_bits_private() {
        let candidate = Boolean::<Circuit>::new(Mode::Private, true);
        check_from_bits_le("Private", true, Mode::Private, &candidate, 0, 0, 0, 0);
        check_from_bits_be("Private", true, Mode::Private, &candidate, 0, 0, 0, 0);

        // Check that casting produces the correct constraints.
        {
            check_from_bits_le("Constant", true, Mode::Constant, &candidate, 1, 0, 0, 1);
            check_from_bits_be("Constant", true, Mode::Constant, &candidate, 1, 0, 0, 1);

            check_from_bits_le("Public", true, Mode::Public, &candidate, 0, 1, 0, 1);
            check_from_bits_be("Public", true, Mode::Public, &candidate, 0, 1, 0, 1);
        }

        let candidate = Boolean::<Circuit>::new(Mode::Private, false);
        check_from_bits_le("Private", false, Mode::Private, &candidate, 0, 0, 0, 0);
        check_from_bits_be("Private", false, Mode::Private, &candidate, 0, 0, 0, 0);

        // Check that casting produces the correct constraints.
        {
            check_from_bits_le("Constant", false, Mode::Constant, &candidate, 1, 0, 0, 1);
            check_from_bits_be("Constant", false, Mode::Constant, &candidate, 1, 0, 0, 1);

            check_from_bits_le("Public", false, Mode::Public, &candidate, 0, 1, 0, 1);
            check_from_bits_be("Public", false, Mode::Public, &candidate, 0, 1, 0, 1);
        }
    }
}
