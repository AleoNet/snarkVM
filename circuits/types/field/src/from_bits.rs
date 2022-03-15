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
use snarkvm_utilities::{bytes_from_bits_le, FromBytes};

impl<E: Environment> FromBits for Field<E> {
    type Boolean = Boolean<E>;

    /// Initializes a new base field element from a list of little-endian bits *without* trailing zeros.
    fn from_bits_le(mode: Mode, bits_le: &[Self::Boolean]) -> Self {
        // Retrieve the data and field size.
        let size_in_data_bits = E::BaseField::size_in_data_bits();
        let size_in_bits = E::BaseField::size_in_bits();

        // Ensure the list of booleans is within the allowed capacity.
        let num_bits = bits_le.len();
        if num_bits > size_in_bits {
            E::halt(format!("Attempted to instantiate a {size_in_bits}-bit field with {num_bits} bits"))
        }

        // Reconstruct the bits as a linear combination representing the original field value.
        // `output` := (2^i * b_i + ... + 2^0 * b_0)
        let mut output = Field::zero();
        let mut coefficient = Field::one();
        for bit in bits_le {
            output += Field::from(bit) * &coefficient;
            coefficient = coefficient.double();
        }

        // TODO (howardwu): This check is insufficient. We need to check that we are within the field modulus.
        // If the number of bits is equivalent to the field size in bits, construct a witness.
        if num_bits > size_in_data_bits {
            // Construct the field value from the given bits.
            let witness_bytes = bytes_from_bits_le(&bits_le.iter().map(|bit| bit.eject_value()).collect::<Vec<_>>());
            let witness = E::BaseField::from_bytes_le(&witness_bytes)
                .unwrap_or_else(|error| E::halt(format!("Failed to construct base field from bytes: {error}")));

            // Initialize a new candidate field.
            let candidate = Field::<E>::new(mode, witness);

            // Ensure `output` == `candidate`
            E::assert_eq(&output, candidate);
        }

        output
    }

    /// Initializes a new base field element from a list of big-endian bits *without* leading zeros.
    fn from_bits_be(mode: Mode, bits_be: &[Self::Boolean]) -> Self {
        // Reverse the given bits from big-endian into little-endian.
        // Note: This is safe as the bit representation is consistent (there are no leading zeros).
        let mut bits_le = bits_be.to_vec();
        bits_le.reverse();

        Self::from_bits_le(mode, &bits_le)
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
            let expected: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            let candidate = Field::<Circuit>::new(mode, expected).to_bits_le();

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = Field::<Circuit>::from_bits_le(mode, &candidate);
                assert_eq!(expected, candidate.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
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
            let expected: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            let candidate = Field::<Circuit>::new(mode, expected).to_bits_be();

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = Field::<Circuit>::from_bits_be(mode, &candidate);
                assert_eq!(expected, candidate.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    #[test]
    fn test_from_bits_le_constant() {
        check_from_bits_le(Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_le_public() {
        check_from_bits_le(Mode::Public, 0, 1, 0, 1);
    }

    #[test]
    fn test_from_bits_le_private() {
        check_from_bits_le(Mode::Private, 0, 0, 1, 1);
    }

    #[test]
    fn test_from_bits_be_constant() {
        check_from_bits_be(Mode::Constant, 1, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_be_public() {
        check_from_bits_be(Mode::Public, 0, 1, 0, 1);
    }

    #[test]
    fn test_from_bits_be_private() {
        check_from_bits_be(Mode::Private, 0, 0, 1, 1);
    }
}
