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
use snarkvm_utilities::{FromBytes, ToBytes};

impl<E: Environment> FromBits for Scalar<E> {
    type Boolean = Boolean<E>;

    /// Initializes a new scalar field element from a list of little-endian bits *without* trailing zeros.
    fn from_bits_le(bits_le: &[Self::Boolean]) -> Self {
        // Retrieve the data and scalar size.
        let size_in_data_bits = E::ScalarField::size_in_data_bits();
        let size_in_bits = E::ScalarField::size_in_bits();

        // Ensure the list of booleans is within the allowed capacity.
        let num_bits = bits_le.len();
        if num_bits > size_in_bits {
            E::halt(format!("Attempted to instantiate a {size_in_bits}-bit scalar with {num_bits} bits"))
        }

        // Construct the candidate scalar field element.
        let output = Scalar { bits_le: bits_le.to_vec() };

        // If the number of bits is equivalent to the scalar size in bits,
        // ensure the scalar is below the scalar field modulus.
        if num_bits > size_in_data_bits {
            // Initialize the scalar field modulus as a constant base field variable.
            //
            // Note: We are reconstituting the scalar field into a base field here in order to check
            // that the scalar was synthesized correctly. This is safe as the scalar field modulus
            // is less that the base field modulus, and thus will always fit in a base field element.
            let modulus = Field::constant(match E::ScalarField::modulus().to_bytes_le() {
                Ok(modulus_bytes) => match E::BaseField::from_bytes_le(&modulus_bytes) {
                    Ok(modulus) => modulus,
                    Err(error) => E::halt(format!("Failed to load the scalar modulus as a constant: {error}")),
                },
                Err(error) => E::halt(format!("Failed to retrieve the scalar modulus as bytes: {error}")),
            });

            // Ensure `output` is less than `E::ScalarField::modulus()`.
            E::assert(output.to_field().is_less_than(&modulus));
        }

        output
    }

    /// Initializes a new scalar field element from a list of big-endian bits *without* leading zeros.
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
    use snarkvm_circuits_environment::Circuit;
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
            let candidate = Scalar::<Circuit>::new(mode, expected).to_bits_le();

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = Scalar::<Circuit>::from_bits_le(&candidate);
                assert_eq!(expected, candidate.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
            Circuit::reset();
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
            let candidate = Scalar::<Circuit>::new(mode, expected).to_bits_be();

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = Scalar::<Circuit>::from_bits_be(&candidate);
                assert_eq!(expected, candidate.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
            Circuit::reset();
        }
    }

    #[test]
    fn test_from_bits_le_constant() {
        check_from_bits_le(Mode::Constant, 507, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_le_public() {
        check_from_bits_le(Mode::Public, 254, 0, 769, 771);
    }

    #[test]
    fn test_from_bits_le_private() {
        check_from_bits_le(Mode::Private, 254, 0, 769, 771);
    }

    #[test]
    fn test_from_bits_be_constant() {
        check_from_bits_be(Mode::Constant, 507, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_be_public() {
        check_from_bits_be(Mode::Public, 254, 0, 769, 771);
    }

    #[test]
    fn test_from_bits_be_private() {
        check_from_bits_be(Mode::Private, 254, 0, 769, 771);
    }
}
