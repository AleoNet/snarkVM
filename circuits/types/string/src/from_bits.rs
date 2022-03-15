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

impl<E: Environment> FromBits for StringType<E> {
    type Boolean = Boolean<E>;

    /// Initializes a new string from a list of little-endian bits *with* trailing zeros (to byte-alignment).
    fn from_bits_le(mode: Mode, bits_le: &[Self::Boolean]) -> Self {
        // Ensure the list of booleans is byte-aligned.
        let num_bits = bits_le.len();
        if num_bits % 8 != 0 {
            E::halt(format!("Attempted to instantiate a {num_bits}-bit string, which is not byte-aligned"))
        }

        // Construct the candidate string.
        let candidate = StringType { bytes: bits_le.chunks(8).map(|chunk| U8::from_bits_le(mode, chunk)).collect() };

        // Ensure the mode in the given bits are consistent with the desired mode.
        // If they do not match, proceed to construct a new string, and check that it is well-formed.
        match candidate.eject_mode() == mode {
            true => candidate,
            false => {
                // Construct a new string as a witness.
                let output = StringType::new(mode, &candidate.eject_value());
                // Ensure `output` == `candidate`, by packing into fields and checking equivalence.
                for (output_field, candidate_field) in output.to_fields().iter().zip_eq(&candidate.to_fields()) {
                    E::assert_eq(output_field, candidate_field);
                }
                // Return the new string.
                output
            }
        }
    }

    /// Initializes a new scalar field element from a list of big-endian bits *with* leading zeros (to byte-alignment).
    fn from_bits_be(mode: Mode, bits_be: &[Self::Boolean]) -> Self {
        // Reverse the given bits from big-endian into little-endian.
        // Note: This is safe as the bit representation is consistent (there are leading zeros).
        let mut bits_le = bits_be.to_vec();
        bits_le.reverse();

        Self::from_bits_le(mode, &bits_le)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::test_rng;

    use rand::Rng;

    const ITERATIONS: u32 = 100;

    fn check_from_bits_le(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let rng = &mut test_rng();

        for i in 0..ITERATIONS {
            // Sample a random string. Take 1/4th to ensure we fit for all code points.
            let expected: String = (0..(Circuit::NUM_STRING_BYTES - i) / 4).map(|_| rng.gen::<char>()).collect();
            let expected_num_bytes = expected.len();
            assert!(expected_num_bytes <= Circuit::NUM_STRING_BYTES as usize);

            let candidate = StringType::<Circuit>::new(mode, &expected).to_bits_le();

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = StringType::<Circuit>::from_bits_le(mode, &candidate);
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
        let rng = &mut test_rng();

        for i in 0..ITERATIONS {
            // Sample a random string. Take 1/4th to ensure we fit for all code points.
            let expected: String = (0..(Circuit::NUM_STRING_BYTES - i) / 4).map(|_| rng.gen::<char>()).collect();
            let expected_num_bytes = expected.len();
            assert!(expected_num_bytes <= Circuit::NUM_STRING_BYTES as usize);

            let candidate = StringType::<Circuit>::new(mode, &expected).to_bits_be();

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = StringType::<Circuit>::from_bits_be(mode, &candidate);
                assert_eq!(expected, candidate.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
            Circuit::reset();
        }
    }

    #[test]
    fn test_from_bits_le_constant() {
        check_from_bits_le(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_le_public() {
        check_from_bits_le(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_le_private() {
        check_from_bits_le(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_be_constant() {
        check_from_bits_be(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_be_public() {
        check_from_bits_be(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_be_private() {
        check_from_bits_be(Mode::Private, 0, 0, 0, 0);
    }
}
