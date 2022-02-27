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

impl<E: Environment, I: IntegerType> FromBits for Integer<E, I> {
    type Boolean = Boolean<E>;

    /// Initializes a new integer from a list of little-endian bits *with* trailing zeros.
    fn from_bits_le(mode: Mode, bits_le: &[Self::Boolean]) -> Self {
        // Ensure the number of booleans is the correct capacity.
        if bits_le.len() != I::BITS {
            E::halt(format!("Attempted to instantiate a {}-bit integer with {} bits", I::BITS, bits_le.len()))
        }

        // Construct a candidate integer.
        let candidate = Integer { bits_le: bits_le.to_vec(), phantom: Default::default() };

        // Ensure the mode in the given bits are consistent, with the desired mode.
        // If they do not match, proceed to construct a new integer, and check that it is well-formed.
        match candidate.eject_mode() == mode {
            true => candidate,
            false => {
                // Construct a new integer as a witness.
                let output = Integer::new(mode, candidate.eject_value());
                // Ensure `output` == `candidate`.
                E::assert_eq(&output, &candidate);
                // Return the new integer.
                output
            }
        }
    }

    /// Initializes a new integer from a list of big-endian bits *with* leading zeros.
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
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 128;

    fn check_from_bits_le<I: IntegerType>(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: I = UniformRand::rand(&mut thread_rng());
            let candidate = Integer::<Circuit, I>::new(mode, expected).to_bits_le();

            Circuit::scoped(&format!("{} {}", mode, i), || {
                let candidate = Integer::<Circuit, I>::from_bits_le(mode, &candidate);
                assert_eq!(expected, candidate.eject_value());

                assert_eq!(num_constants, Circuit::num_constants_in_scope(), "(num_constants)");
                assert_eq!(num_public, Circuit::num_public_in_scope(), "(num_public)");
                assert_eq!(num_private, Circuit::num_private_in_scope(), "(num_private)");
                assert_eq!(num_constraints, Circuit::num_constraints_in_scope(), "(num_constraints)");
                assert!(Circuit::is_satisfied(), "(is_satisfied)");
            });
        }
    }

    fn check_from_bits_be<I: IntegerType>(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: I = UniformRand::rand(&mut thread_rng());
            let candidate = Integer::<Circuit, I>::new(mode, expected).to_bits_be();

            Circuit::scoped(&format!("{} {}", mode, i), || {
                let candidate = Integer::<Circuit, I>::from_bits_be(mode, &candidate);
                assert_eq!(expected, candidate.eject_value());

                assert_eq!(num_constants, Circuit::num_constants_in_scope(), "(num_constants)");
                assert_eq!(num_public, Circuit::num_public_in_scope(), "(num_public)");
                assert_eq!(num_private, Circuit::num_private_in_scope(), "(num_private)");
                assert_eq!(num_constraints, Circuit::num_constraints_in_scope(), "(num_constraints)");
                assert!(Circuit::is_satisfied(), "(is_satisfied)");
            });
        }
    }

    #[test]
    fn test_from_bits_le_constant() {
        type I = i64;
        check_from_bits_le::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_le_public() {
        type I = i64;
        check_from_bits_le::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_le_private() {
        type I = i64;
        check_from_bits_le::<I>(Mode::Private, 0, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_be_constant() {
        type I = i64;
        check_from_bits_be::<I>(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_be_public() {
        type I = i64;
        check_from_bits_be::<I>(Mode::Public, 0, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_be_private() {
        type I = i64;
        check_from_bits_be::<I>(Mode::Private, 0, 0, 0, 0);
    }
}
