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
use crate::BaseField;
use snarkvm_utilities::{from_bits_le_to_bytes_le, FromBytes};

impl<E: Environment> FromBits for Scalar<E> {
    type Boolean = Boolean<E>;

    /// Initializes a new scalar field element from a list of little-endian bits *without* trailing zeros.
    fn from_bits_le(mode: Mode, bits_le: &[Self::Boolean]) -> Self {
        // TODO (howardwu): Contemplate how to handle the CAPACITY vs. BITS case.
        // Ensure the list of booleans is within the allowed capacity.
        let mut bits_le = bits_le.to_vec();
        match bits_le.len() <= E::ScalarField::size_in_bits() {
            true => bits_le.resize(E::ScalarField::size_in_bits(), Boolean::new(Mode::Constant, false)),
            false => E::halt(format!(
                "Attempted to instantiate a {}-bit scalar field element with {} bits",
                E::ScalarField::size_in_bits(),
                bits_le.len()
            )),
        }

        // Construct the field value from the given bits.
        let witness = match E::ScalarField::from_bytes_le(&from_bits_le_to_bytes_le(
            &bits_le.iter().map(|bit| bit.eject_value()).collect::<Vec<_>>(),
        )) {
            Ok(value) => value,
            Err(error) => E::halt(format!("Failed to convert a list of booleans into a scalar field element. {}", error)),
        };

        let output = Scalar::new(mode, witness);

        // Reconstruct the bits as a linear combination representing the original field value.
        //
        // Note: We are reconstituting the scalar field into a base field here in order to check
        // that the scalar was synthesized correctly. This is safe as the scalar field modulus
        // is less that the base field modulus, and thus will always fit in a base field element.
        let mut accumulator = BaseField::zero();
        let mut coefficient = BaseField::one();
        for bit in &bits_le {
            accumulator += BaseField::from(bit) * &coefficient;
            coefficient = coefficient.double();
        }

        // Ensure `output` * 1 == (2^i * b_i + ... + 2^0 * b_0)
        E::enforce(|| (&output, E::one(), accumulator));

        output
    }

    /// Initializes a new scalar field element from a list of big-endian bits *without* leading zeros.
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
    use crate::{assert_circuit, Circuit};
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

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
            let expected: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut thread_rng());
            let candidate = Scalar::<Circuit>::new(mode, expected).to_bits_le();

            Circuit::scoped(&format!("{} {}", mode, i), || {
                let candidate = Scalar::<Circuit>::from_bits_le(mode, &candidate);
                assert_eq!(expected, candidate.eject_value());
                assert_circuit!(num_constants, num_public, num_private, num_constraints);
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
            let expected: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut thread_rng());
            let candidate = Scalar::<Circuit>::new(mode, expected).to_bits_be();

            Circuit::scoped(&format!("{} {}", mode, i), || {
                let candidate = Scalar::<Circuit>::from_bits_be(mode, &candidate);
                assert_eq!(expected, candidate.eject_value());
                assert_circuit!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    #[test]
    fn test_from_bits_le_constant() {
        check_from_bits_le(Mode::Constant, 2, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_le_public() {
        check_from_bits_le(Mode::Public, 1, 1, 0, 1);
    }

    #[test]
    fn test_from_bits_le_private() {
        check_from_bits_le(Mode::Private, 1, 0, 1, 1);
    }

    #[test]
    fn test_from_bits_be_constant() {
        check_from_bits_be(Mode::Constant, 2, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_be_public() {
        check_from_bits_be(Mode::Public, 1, 1, 0, 1);
    }

    #[test]
    fn test_from_bits_be_private() {
        check_from_bits_be(Mode::Private, 1, 0, 1, 1);
    }
}
