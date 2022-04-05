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

use std::iter;

impl<E: Environment> FromBits for Scalar<E> {
    type Boolean = Boolean<E>;

    /// Initializes a new scalar field element from a list of little-endian bits.
    /// If the length of the list is greater than `E::ScalarField::size_in_bits()`, the excess bits
    /// are checked to ensure they are all zero.
    /// If the length of the list is less than or equal to `E::ScalarField::size_in_bits()`, `bits_le`
    /// is padded with zeros to the right to match the size of the scalar field.
    fn from_bits_le(bits_le: &[Self::Boolean]) -> Self {
        // Retrieve the data and field size.
        let size_in_data_bits = E::ScalarField::size_in_data_bits();
        let size_in_bits = E::ScalarField::size_in_bits();

        // Ensure the list of booleans is within the allowed size in bits.
        let num_bits = bits_le.len();
        if num_bits > size_in_bits {
            // Check if all excess bits are zero.
            let should_be_zero = bits_le[size_in_bits..].iter().fold(Boolean::constant(false), |acc, bit| acc | bit);
            // Ensure `should_be_zero` is zero.
            match should_be_zero.is_constant() {
                true => match should_be_zero.eject_value() {
                    false => (), // Constraint is satisfied.
                    true => {
                        E::halt("Detected nonzero excess bits while initializing a scalar field element from bits.")
                    }
                },
                false => E::assert_eq(E::zero(), should_be_zero),
            }
        }

        // If the number of bits is greater than `size_in_data_bits`, then check that it is a valid field element.
        if num_bits > size_in_data_bits {
            // Retrieve the modulus & subtract by 1 as we'll check `bits_le` is less than or *equal* to this value.
            // (For advanced users) ScalarField::MODULUS - 1 is equivalent to -1 in the field.
            let modulus_minus_one = -E::ScalarField::one();

            // Pad `bits_le` with zeros to the size of the scalar field modulus, if necessary.
            let boolean_false = Boolean::constant(false);
            let padded_bits_le = bits_le.iter().chain(iter::repeat(&boolean_false)).take(size_in_bits);

            // Zip `modulus_minus_one` and `padded_bits_le` together and construct a check on the sequence of bit pairs.
            // See `Field::is_less_than` for more details.
            let modulus_minus_one_less_than_bits = modulus_minus_one.to_bits_le().iter().zip_eq(padded_bits_le).fold(
                Boolean::constant(false),
                |rest_is_less, (modulus_minus_one_bit, other_bit)| {
                    if *modulus_minus_one_bit {
                        Boolean::ternary(&!other_bit, other_bit, &rest_is_less)
                    } else {
                        Boolean::ternary(other_bit, other_bit, &rest_is_less)
                    }
                },
            );

            // Enforce that ScalarField::MODULUS - 1 is not less than the field element given by `bits_le`.
            // In other words, enforce that ScalarField::MODULUS - 1 is greater than or equal to the field element given by `bits_le`.
            match modulus_minus_one_less_than_bits.is_constant() {
                true => match modulus_minus_one_less_than_bits.eject_value() {
                    false => (), // Constraint is satisfied.
                    true => {
                        E::halt("Detected nonzero excess bits while initializing a scalar field element from bits.")
                    }
                },
                false => E::assert(!modulus_minus_one_less_than_bits),
            }
        }

        // Construct the sanitized list of bits, resizing up if necessary.
        let mut bits_le = bits_le.iter().take(size_in_bits).cloned().collect::<Vec<_>>();
        bits_le.resize(size_in_bits, Boolean::constant(false));

        Scalar { bits_le }
    }

    /// Initializes a new scalar field element from a list of big-endian bits.
    /// If the length of the list is greater than `E::ScalarField::size_in_bits()`, the excess bits
    /// are checked to ensure they are all zero.
    /// If the length of the list is less than or equal to `E::ScalarField::size_in_bits()`, `bits_be`
    /// is padded with zeros to the left to match the size of the scalar field.
    fn from_bits_be(bits_be: &[Self::Boolean]) -> Self {
        // Reverse the given bits from big-endian into little-endian.
        // Note: This is safe as the bit representation is consistent (there are no leading zeros).
        let mut bits_le = bits_be.to_vec();
        bits_le.reverse();

        Self::from_bits_le(&bits_le)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::{assert_scope_fails, Circuit};
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 100;

    fn check_from_bits_le(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut test_rng());
            let given_bits = Scalar::<Circuit>::new(mode, expected).to_bits_le();
            let expected_size_in_bits = given_bits.len();

            // Check the case where `bits_le` is less than the scalar field modulus.
            Circuit::scope(format!("{mode} {i}"), || {
                let candidate = Scalar::<Circuit>::from_bits_le(&given_bits);
                assert_eq!(expected, candidate.eject_value());
                assert_eq!(expected_size_in_bits, candidate.bits_le.len());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });

            // Add excess zero bits.
            let candidate = vec![given_bits.clone(), vec![Boolean::new(mode, false); i]].concat();

            Circuit::scope(&format!("Excess Zero: {} {}", mode, i), || {
                let candidate = Scalar::<Circuit>::from_bits_le(&candidate);
                assert_eq!(expected, candidate.eject_value());
                assert_eq!(expected_size_in_bits, candidate.bits_le.len());
                match mode.is_constant() {
                    true => assert_scope!(num_constants, num_public, num_private, num_constraints),
                    // `num_private` gets 1 free excess bit, then is incremented by one for each excess bit.
                    // `num_constraints` is incremented by one for each excess bit.
                    false => {
                        assert_scope!(num_constants, num_public, num_private + i.saturating_sub(1), num_constraints + i)
                    }
                };
            });

            // Add excess one bits.
            let candidate = vec![given_bits, vec![Boolean::new(mode, true); i + 1]].concat();

            match mode.is_constant() {
                true => assert!(std::panic::catch_unwind(|| Scalar::<Circuit>::from_bits_le(&candidate)).is_err()),
                _ => {
                    Circuit::scope(format!("Excess One: {mode}"), || {
                        let _ = Scalar::<Circuit>::from_bits_le(&candidate);
                        assert_scope_fails!(num_constants, num_public, num_private + i, num_constraints + i + 1);
                    });
                }
            }
        }

        // Check the case where `bits_le` is equal to the scalar field modulus.
        let modulus = <Circuit as Environment>::ScalarField::modulus()
            .to_bits_le()
            .iter()
            .map(|b| Boolean::new(mode, *b))
            .take(<Circuit as Environment>::ScalarField::size_in_bits())
            .collect::<Vec<_>>();

        match mode.is_constant() {
            true => assert!(std::panic::catch_unwind(|| Scalar::<Circuit>::from_bits_le(&modulus)).is_err()),
            _ => {
                Circuit::scope(format!("Modulus: {mode}"), || {
                    let _ = Scalar::<Circuit>::from_bits_le(&modulus);
                    assert_scope_fails!(num_constants, num_public, num_private, num_constraints);
                });
            }
        }
    }

    fn check_from_bits_be(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut test_rng());
            let given_bits = Scalar::<Circuit>::new(mode, expected).to_bits_be();
            let expected_size_in_bits = given_bits.len();

            // Check the case where `bits_be` is less than the scalar field modulus.
            Circuit::scope(format!("{mode} {i}"), || {
                let candidate = Scalar::<Circuit>::from_bits_be(&given_bits);
                assert_eq!(expected, candidate.eject_value());
                assert_eq!(expected_size_in_bits, candidate.to_bits_be().len());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });

            // Add excess zero bits.
            let candidate = vec![vec![Boolean::new(mode, false); i], given_bits.clone()].concat();

            Circuit::scope(&format!("Excess Zero: {} {}", mode, i), || {
                let candidate = Scalar::<Circuit>::from_bits_be(&candidate);
                assert_eq!(expected, candidate.eject_value());
                assert_eq!(expected_size_in_bits, candidate.bits_le.len());
                match mode.is_constant() {
                    true => assert_scope!(num_constants, num_public, num_private, num_constraints),
                    // `num_private` gets 1 free excess bit, then is incremented by one for each excess bit.
                    // `num_constraints` is incremented by one for each excess bit.
                    false => {
                        assert_scope!(num_constants, num_public, num_private + i.saturating_sub(1), num_constraints + i)
                    }
                };
            });

            // Add excess one bits.
            let candidate = vec![vec![Boolean::new(mode, true); i + 1], given_bits].concat();

            match mode.is_constant() {
                true => assert!(std::panic::catch_unwind(|| Scalar::<Circuit>::from_bits_be(&candidate)).is_err()),
                false => {
                    Circuit::scope(format!("Excess One: {mode}"), || {
                        let _ = Scalar::<Circuit>::from_bits_be(&candidate);
                        assert_scope_fails!(num_constants, num_public, num_private + i, num_constraints + i + 1);
                    });
                }
            }
        }

        // Check the case where `bits_be` is equal to the scalar field modulus.
        let modulus = <Circuit as Environment>::ScalarField::modulus()
            .to_bits_le()
            .iter()
            .map(|b| Boolean::new(mode, *b))
            .take(<Circuit as Environment>::ScalarField::size_in_bits())
            .rev()
            .collect::<Vec<_>>();

        match mode.is_constant() {
            true => assert!(std::panic::catch_unwind(|| Scalar::<Circuit>::from_bits_be(&modulus)).is_err()),
            false => {
                Circuit::scope(format!("Modulus: {mode}"), || {
                    let _ = Scalar::<Circuit>::from_bits_be(&modulus);
                    assert_scope_fails!(num_constants, num_public, num_private, num_constraints);
                });
            }
        }
    }

    #[test]
    fn test_from_bits_le_constant() {
        check_from_bits_le(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_le_public() {
        check_from_bits_le(Mode::Public, 0, 0, 251, 252);
    }

    #[test]
    fn test_from_bits_le_private() {
        check_from_bits_le(Mode::Private, 0, 0, 251, 252);
    }

    #[test]
    fn test_from_bits_be_constant() {
        check_from_bits_be(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_be_public() {
        check_from_bits_be(Mode::Public, 0, 0, 251, 252);
    }

    #[test]
    fn test_from_bits_be_private() {
        check_from_bits_be(Mode::Private, 0, 0, 251, 252);
    }
}
