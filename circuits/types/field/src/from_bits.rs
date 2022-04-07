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

impl<E: Environment> FromBits for Field<E> {
    type Boolean = Boolean<E>;

    /// Initializes a new base field element from a list of little-endian bits *without* trailing zeros.
    fn from_bits_le(bits_le: &[Self::Boolean]) -> Self {
        // Retrieve the data and field size.
        let size_in_data_bits = E::BaseField::size_in_data_bits();
        let size_in_bits = E::BaseField::size_in_bits();

        // Ensure the list of booleans is within the allowed size in bits.
        let num_bits = bits_le.len();
        if num_bits > size_in_bits {
            // Check if all excess bits are zero.
            let should_be_zero = bits_le[size_in_bits..].iter().fold(Boolean::constant(false), |acc, bit| acc | bit);
            // Ensure `should_be_zero` is zero.
            E::assert_eq(E::zero(), should_be_zero);
        }

        // Reconstruct the bits as a linear combination representing the original field value.
        // `output` := (2^i * b_i + ... + 2^0 * b_0)
        let mut output = Field::zero();
        let mut coefficient = Field::one();
        for bit in bits_le.iter().take(size_in_bits) {
            output += Field::from_boolean(bit) * &coefficient;
            coefficient = coefficient.double();
        }

        // If the number of bits is equivalent to the field size in bits (or greater),
        // ensure the reconstructed field element lies within the field modulus.
        if num_bits > size_in_data_bits {
            // Retrieve the modulus & subtract by 1 as we'll check `output.bits_le` is less than or *equal* to this value.
            // (For advanced users) BaseField::MODULUS - 1 is equivalent to -1 in the field.
            let modulus = -E::BaseField::one();

            // Initialize an iterator for big-endian bits, skipping the excess bits, which are checked above.
            let mut bits_be = bits_le.iter().rev().skip(bits_le.len() - size_in_bits);

            // Initialize trackers for the sequence of ones.
            let mut previous = Boolean::constant(true);
            let mut sequence = vec![];

            for (modulus_bit, current_bit) in modulus.to_bits_be().iter().zip_eq(&mut bits_be) {
                match modulus_bit {
                    // This bit *continues* a sequence of ones.
                    true => sequence.push(current_bit),
                    // This bit *breaks* a sequence of ones.
                    false => {
                        // Process the previous sequence and reset for the new sequence.
                        if !sequence.is_empty() {
                            // Check if all bits were true.
                            previous = sequence.iter().fold(previous, |a, b| a & *b);
                            sequence.clear();
                        }

                        // Ensure either `previous` or `current_bit` must be false: `previous` NAND `current_bit`
                        //
                        // If `previous` is true, `current_bit` must be false, or it is not in the field.
                        // If `previous` is false, `current_bit` can be true or false.
                        // Thus, either `previous` or `current_bit` must be false.
                        E::assert(previous.nand(current_bit));
                    }
                }
            }
            // The sequence will always finish empty, because we subtracted 1 from the `modulus`.
            debug_assert!(sequence.is_empty());
        }

        // Construct the sanitized list of bits, resizing up if necessary.
        let mut bits_le = bits_le.iter().take(size_in_bits).cloned().collect::<Vec<_>>();
        bits_le.resize(size_in_bits, Boolean::constant(false));

        // Store the little-endian bits in the output.
        if output.bits_le.set(bits_le).is_err() {
            E::halt("Detected corrupt internal state for the bits of a field element")
        }

        output
    }

    /// Initializes a new base field element from a list of big-endian bits *without* leading zeros.
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
            let expected: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            let given_bits = Field::<Circuit>::new(mode, expected).to_bits_le();
            let expected_size_in_bits = given_bits.len();

            Circuit::scope(format!("{mode} {i}"), || {
                let candidate = Field::<Circuit>::from_bits_le(&given_bits);
                assert_eq!(expected, candidate.eject_value());
                assert_eq!(expected_size_in_bits, candidate.bits_le.get().expect("Caching failed").len());
                assert_scope!(num_constants, num_public, num_private, num_constraints);

                // Ensure a subsequent call to `to_bits_le` does not incur additional costs.
                let candidate_bits = candidate.to_bits_le();
                assert_eq!(expected_size_in_bits, candidate_bits.len());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });

            // Add excess zero bits.
            let candidate = vec![given_bits, vec![Boolean::new(mode, false); i]].concat();

            Circuit::scope(&format!("Excess {} {}", mode, i), || {
                let candidate = Field::<Circuit>::from_bits_le(&candidate);
                assert_eq!(expected, candidate.eject_value());
                assert_eq!(expected_size_in_bits, candidate.bits_le.get().expect("Caching failed").len());
                match mode.is_constant() {
                    true => assert_scope!(num_constants, num_public, num_private, num_constraints),
                    // `num_private` gets 1 free excess bit, then is incremented by one for each excess bit.
                    // `num_constraints` is incremented by one for each excess bit.
                    false => {
                        assert_scope!(num_constants, num_public, num_private + i.saturating_sub(1), num_constraints + i)
                    }
                };
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
            let given_bits = Field::<Circuit>::new(mode, expected).to_bits_be();
            let expected_size_in_bits = given_bits.len();

            Circuit::scope(format!("{mode} {i}"), || {
                let candidate = Field::<Circuit>::from_bits_be(&given_bits);
                assert_eq!(expected, candidate.eject_value());
                assert_eq!(expected_size_in_bits, candidate.bits_le.get().expect("Caching failed").len());
                assert_scope!(num_constants, num_public, num_private, num_constraints);

                // Ensure a subsequent call to `to_bits_be` does not incur additional costs.
                let candidate_bits = candidate.to_bits_be();
                assert_eq!(expected_size_in_bits, candidate_bits.len());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });

            // Add excess zero bits.
            let candidate = vec![vec![Boolean::new(mode, false); i], given_bits].concat();

            Circuit::scope(&format!("Excess {} {}", mode, i), || {
                let candidate = Field::<Circuit>::from_bits_be(&candidate);
                assert_eq!(expected, candidate.eject_value());
                assert_eq!(expected_size_in_bits, candidate.bits_le.get().expect("Caching failed").len());
                match mode.is_constant() {
                    true => assert_scope!(num_constants, num_public, num_private, num_constraints),
                    // `num_private` gets 1 free excess bit, then is incremented by one for each excess bit.
                    // `num_constraints` is incremented by one for each excess bit.
                    false => {
                        assert_scope!(num_constants, num_public, num_private + i.saturating_sub(1), num_constraints + i)
                    }
                };
            });
        }
    }

    #[test]
    fn test_from_bits_le_constant() {
        check_from_bits_le(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_le_public() {
        check_from_bits_le(Mode::Public, 0, 0, 252, 418);
    }

    #[test]
    fn test_from_bits_le_private() {
        check_from_bits_le(Mode::Private, 0, 0, 252, 418);
    }

    #[test]
    fn test_from_bits_be_constant() {
        check_from_bits_be(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_be_public() {
        check_from_bits_be(Mode::Public, 0, 0, 252, 418);
    }

    #[test]
    fn test_from_bits_be_private() {
        check_from_bits_be(Mode::Private, 0, 0, 252, 418);
    }
}
