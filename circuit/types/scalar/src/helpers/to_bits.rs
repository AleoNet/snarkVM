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

impl<E: Environment> ToBits for Scalar<E> {
    type Boolean = Boolean<E>;

    /// Outputs the little-endian bit representation of `self` *without* trailing zeros.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        (&self).to_bits_le()
    }

    /// Outputs the big-endian bit representation of `self` *without* leading zeros.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        (&self).to_bits_be()
    }
}

impl<E: Environment> ToBits for &Scalar<E> {
    type Boolean = Boolean<E>;

    /// Outputs the little-endian bit representation of `self` *without* trailing zeros.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        self.bits_le
            .get_or_init(|| {
                // Note: We are reconstituting the scalar field into a base field.
                // This is safe as the scalar field modulus is less than the base field modulus,
                // and thus will always fit within a single base field element.
                debug_assert!(
                    console::Scalar::<E::Network>::size_in_bits() < console::Field::<E::Network>::size_in_bits()
                );

                // Construct a vector of `Boolean`s comprising the bits of the scalar value.
                self.field.to_lower_bits_le(console::Scalar::<E::Network>::size_in_bits())
            })
            .clone()
    }

    /// Outputs the big-endian bit representation of `self` *without* leading zeros.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        let mut bits_le = self.to_bits_le();
        bits_le.reverse();
        bits_le
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    fn check_to_bits_le(
        name: &str,
        expected: &[bool],
        candidate: &Scalar<Circuit>,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        let expected_number_of_bits = console::Scalar::<<Circuit as Environment>::Network>::size_in_bits();

        Circuit::scope(name, || {
            let candidate_bits = candidate.to_bits_le();
            assert_eq!(expected_number_of_bits, candidate_bits.len());
            for (expected_bit, candidate_bit) in expected.iter().zip_eq(candidate_bits.iter()) {
                assert_eq!(*expected_bit, candidate_bit.eject_value());
            }
            assert_scope!(num_constants, num_public, num_private, num_constraints);

            // Ensure a second call incurs no additional cost.
            let _candidate_bits = candidate.to_bits_le();
            assert_scope!(num_constants, num_public, num_private, num_constraints);
        });
    }

    fn check_to_bits_be(
        name: &str,
        expected: &[bool],
        candidate: Scalar<Circuit>,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        let expected_number_of_bits = console::Scalar::<<Circuit as Environment>::Network>::size_in_bits();

        Circuit::scope(name, || {
            let candidate_bits = candidate.to_bits_be();
            assert_eq!(expected_number_of_bits, candidate_bits.len());
            for (expected_bit, candidate_bit) in expected.iter().zip_eq(candidate_bits.iter()) {
                assert_eq!(*expected_bit, candidate_bit.eject_value());
            }
            assert_scope!(num_constants, num_public, num_private, num_constraints);

            // Ensure a second call incurs no additional cost.
            let _candidate_bits = candidate.to_bits_be();
            assert_scope!(num_constants, num_public, num_private, num_constraints);
        });
    }

    #[test]
    fn test_to_bits_le_constant() {
        let expected = Uniform::rand(&mut test_rng());
        let candidate = Scalar::<Circuit>::new(Mode::Constant, expected);
        check_to_bits_le("Constant", &expected.to_bits_le(), &candidate, 251, 0, 0, 0);
    }

    #[test]
    fn test_to_bits_be_constant() {
        let expected = Uniform::rand(&mut test_rng());
        let candidate = Scalar::<Circuit>::new(Mode::Constant, expected);
        check_to_bits_be("Constant", &expected.to_bits_be(), candidate, 251, 0, 0, 0);
    }

    #[test]
    fn test_to_bits_le_public() {
        let expected = Uniform::rand(&mut test_rng());
        let candidate = Scalar::<Circuit>::new(Mode::Public, expected);
        check_to_bits_le("Public", &expected.to_bits_le(), &candidate, 0, 0, 251, 252);
    }

    #[test]
    fn test_to_bits_be_public() {
        let expected = Uniform::rand(&mut test_rng());
        let candidate = Scalar::<Circuit>::new(Mode::Public, expected);
        check_to_bits_be("Public", &expected.to_bits_be(), candidate, 0, 0, 251, 252);
    }

    #[test]
    fn test_to_bits_le_private() {
        let expected = Uniform::rand(&mut test_rng());
        let candidate = Scalar::<Circuit>::new(Mode::Private, expected);
        check_to_bits_le("Private", &expected.to_bits_le(), &candidate, 0, 0, 251, 252);
    }

    #[test]
    fn test_to_bits_be_private() {
        let expected = Uniform::rand(&mut test_rng());
        let candidate = Scalar::<Circuit>::new(Mode::Private, expected);
        check_to_bits_be("Private", &expected.to_bits_be(), candidate, 0, 0, 251, 252);
    }

    #[test]
    fn test_one() {
        /// Checks that the field element, when converted to little-endian bits, is well-formed.
        fn check_bits_le(candidate: Scalar<Circuit>) {
            for (i, bit) in candidate.to_bits_le().iter().enumerate() {
                match i == 0 {
                    true => assert!(bit.eject_value()),
                    false => assert!(!bit.eject_value()),
                }
            }
        }

        /// Checks that the field element, when converted to big-endian bits, is well-formed.
        fn check_bits_be(candidate: Scalar<Circuit>) {
            for (i, bit) in candidate.to_bits_be().iter().rev().enumerate() {
                match i == 0 {
                    true => assert!(bit.eject_value()),
                    false => assert!(!bit.eject_value()),
                }
            }
        }

        let one = console::Scalar::<<Circuit as Environment>::Network>::one();

        // Constant
        check_bits_le(Scalar::<Circuit>::new(Mode::Constant, one));
        check_bits_be(Scalar::<Circuit>::new(Mode::Constant, one));
        // Public
        check_bits_le(Scalar::<Circuit>::new(Mode::Public, one));
        check_bits_be(Scalar::<Circuit>::new(Mode::Public, one));
        // Private
        check_bits_le(Scalar::<Circuit>::new(Mode::Private, one));
        check_bits_be(Scalar::<Circuit>::new(Mode::Private, one));
    }
}
