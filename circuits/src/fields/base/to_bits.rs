// Copyright (C) 2019-2021 Aleo Systems Inc.
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

impl<E: Environment> ToBits for BaseField<E> {
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

impl<E: Environment> ToBits for &BaseField<E> {
    type Boolean = Boolean<E>;

    /// Outputs the little-endian bit representation of `self` *without* trailing zeros.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        let mode = match self.is_constant() {
            true => Mode::Constant,
            false => Mode::Private,
        };

        // Construct a vector of `Boolean`s comprising the bits of the field value.
        let bits = self
            .eject_value()
            .to_bits_le()
            .iter()
            .map(|bit| Boolean::new(mode, *bit))
            .collect::<Vec<_>>();

        // Reconstruct the bits as a linear combination representing the original field value.
        let mut accumulator = BaseField::zero();
        let mut coefficient = BaseField::one();
        for bit in &bits {
            accumulator += BaseField::from(bit) * &coefficient;
            coefficient = coefficient.double();
        }

        // Ensure value * 1 == (2^i * b_i + ... + 2^0 * b_0)
        E::assert_eq(*self, accumulator);

        bits
    }

    /// Outputs the big-endian bit representation of `self` *without* leading zeros.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        let mut bits_le = self.to_bits_le();
        bits_le.reverse();
        bits_le
    }
}

impl<E: Environment> BaseField<E> {
    ///
    /// Extracts the lower k bits of a field element that uses n bits.
    /// Requires that the upper n - k bits are zero.
    ///
    pub fn extract_lower_k_bits_le(&self, k: usize) -> Vec<Boolean<E>> {
        if k > 253 {
            E::halt(format!(
                "Attempted to extract {} bits from a 253-bit base field element.",
                k
            ))
        }

        let mode = match self.is_constant() {
            true => Mode::Constant,
            false => Mode::Private,
        };

        // Construct a vector of `Boolean`s comprising the bits of the field value.
        let bits = self
            .eject_value()
            .to_bits_le()
            .iter()
            .take(k)
            .map(|bit| Boolean::new(mode, *bit))
            .collect::<Vec<_>>();

        // Reconstruct the bits as a linear combination representing the original field value.
        let mut accumulator = BaseField::zero();
        let mut coefficient = BaseField::one();
        for bit in &bits {
            accumulator += BaseField::from(bit) * &coefficient;
            coefficient = coefficient.double();
        }

        // Ensure value * 1 == (2^k * b_k + ... + 2^0 * b_0)
        // Enforces that b_n, ..., b_n-k all equal to zero.
        E::assert_eq(self, accumulator);

        bits
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Circuit, Integer};
    use snarkvm_fields::PrimeField;
    use snarkvm_utilities::{from_bytes_le_to_bits_le, FromBytes, ToBytes, UniformRand};

    use crate::helpers::integers::IntegerType;
    use itertools::Itertools;
    use num_traits::Unsigned;
    use rand::thread_rng;

    const ITERATIONS: usize = 100;

    fn check_to_bits_le(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let expected_number_of_bits = <<Circuit as Environment>::BaseField as PrimeField>::size_in_bits();

        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());
            let candidate = BaseField::<Circuit>::new(mode, expected);

            Circuit::scoped(&format!("{} {}", mode, i), |scope| {
                let candidate = candidate.to_bits_le();
                assert_eq!(expected_number_of_bits, candidate.len());
                for (expected_bit, candidate_bit) in expected.to_bits_le().iter().zip_eq(candidate.iter()) {
                    assert_eq!(*expected_bit, candidate_bit.eject_value());
                }

                assert_eq!(num_constants, scope.num_constants_in_scope(), "(num_constants)");
                assert_eq!(num_public, scope.num_public_in_scope(), "(num_public)");
                assert_eq!(num_private, scope.num_private_in_scope(), "(num_private)");
                assert_eq!(num_constraints, scope.num_constraints_in_scope(), "(num_constraints)");
                assert!(Circuit::is_satisfied(), "(is_satisfied)");
            });
        }
    }

    fn check_extract_lower_k_bits_le<I: IntegerType + Unsigned + ToBytes>(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for i in 0..ITERATIONS {
            // Sample a random unsigned integer.
            let value: I = UniformRand::rand(&mut thread_rng());
            let mut field_bytes = value.to_bytes_le().unwrap();
            field_bytes.resize(<Circuit as Environment>::BaseField::size_in_bits(), 0u8); // Note: Pads more than necessary.
            let candidate = BaseField::<Circuit>::new(
                mode,
                <Circuit as Environment>::BaseField::from_bytes_le(&field_bytes).unwrap(),
            );

            let expected_bytes = value.to_bytes_le().unwrap();
            let expected = from_bytes_le_to_bits_le(&expected_bytes);

            Circuit::scoped(&format!("{} {}", mode, i), |scope| {
                let candidate = candidate.extract_lower_k_bits_le(I::BITS);
                assert_eq!(I::BITS, candidate.len());
                for (expected_bit, candidate_bit) in expected.zip_eq(candidate.iter()) {
                    assert_eq!(expected_bit, candidate_bit.eject_value());
                }
                assert_eq!(num_constants, scope.num_constants_in_scope(), "(num_constants)");
                assert_eq!(num_public, scope.num_public_in_scope(), "(num_public)");
                assert_eq!(num_private, scope.num_private_in_scope(), "(num_private)");
                assert_eq!(num_constraints, scope.num_constraints_in_scope(), "(num_constraints)");
                assert!(Circuit::is_satisfied(), "(is_satisfied)");
            });
        }
    }

    fn check_to_bits_be(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let expected_number_of_bits = <<Circuit as Environment>::BaseField as PrimeField>::size_in_bits();

        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());
            let candidate = BaseField::<Circuit>::new(mode, expected);

            Circuit::scoped(&format!("{} {}", mode, i), |scope| {
                let candidate = candidate.to_bits_be();
                assert_eq!(expected_number_of_bits, candidate.len());
                for (expected_bit, candidate_bit) in expected.to_bits_be().iter().zip_eq(candidate.iter()) {
                    assert_eq!(*expected_bit, candidate_bit.eject_value());
                }

                assert_eq!(num_constants, scope.num_constants_in_scope(), "(num_constants)");
                assert_eq!(num_public, scope.num_public_in_scope(), "(num_public)");
                assert_eq!(num_private, scope.num_private_in_scope(), "(num_private)");
                assert_eq!(num_constraints, scope.num_constraints_in_scope(), "(num_constraints)");
                assert!(Circuit::is_satisfied(), "(is_satisfied)");
            });
        }
    }

    #[test]
    fn test_to_bits_le_constant() {
        check_to_bits_le(Mode::Constant, 253, 0, 0, 0);
    }

    #[test]
    fn test_to_bits_le_public() {
        check_to_bits_le(Mode::Public, 0, 0, 253, 254);
    }

    #[test]
    fn test_to_bits_le_private() {
        check_to_bits_le(Mode::Private, 0, 0, 253, 254);
    }

    #[test]
    fn test_extract_lower_8_bits_constant() {
        check_extract_lower_k_bits_le::<u8>(Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_extract_lower_16_bits_constant() {
        check_extract_lower_k_bits_le::<u16>(Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_extract_lower_32_bits_constant() {
        check_extract_lower_k_bits_le::<u32>(Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_extract_lower_64_bits_constant() {
        check_extract_lower_k_bits_le::<u64>(Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_extract_lower_128_bits_constant() {
        check_extract_lower_k_bits_le::<u128>(Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_extract_lower_8_bits_le_public() {
        check_extract_lower_k_bits_le::<u8>(Mode::Public, 0, 0, 8, 9);
    }

    #[test]
    fn test_extract_lower_16_bits_le_public() {
        check_extract_lower_k_bits_le::<u16>(Mode::Public, 0, 0, 16, 17);
    }

    #[test]
    fn test_extract_lower_32_bits_le_public() {
        check_extract_lower_k_bits_le::<u32>(Mode::Public, 0, 0, 32, 33);
    }

    #[test]
    fn test_extract_lower_64_bits_le_public() {
        check_extract_lower_k_bits_le::<u64>(Mode::Public, 0, 0, 64, 65);
    }

    #[test]
    fn test_extract_lower_128_bits_le_public() {
        check_extract_lower_k_bits_le::<u128>(Mode::Public, 0, 0, 128, 129);
    }

    #[test]
    fn test_extract_lower_8_bits_le_private() {
        check_extract_lower_k_bits_le::<u8>(Mode::Private, 0, 0, 8, 9);
    }

    #[test]
    fn test_extract_lower_16_bits_le_private() {
        check_extract_lower_k_bits_le::<u16>(Mode::Private, 0, 0, 16, 17);
    }

    #[test]
    fn test_extract_lower_32_bits_le_private() {
        check_extract_lower_k_bits_le::<u32>(Mode::Private, 0, 0, 32, 33);
    }

    #[test]
    fn test_extract_lower_64_bits_le_private() {
        check_extract_lower_k_bits_le::<u64>(Mode::Private, 0, 0, 64, 65);
    }

    #[test]
    fn test_extract_lower_128_bits_le_private() {
        check_extract_lower_k_bits_le::<u128>(Mode::Private, 0, 0, 128, 129);
    }

    #[test]
    fn test_to_bits_be_constant() {
        check_to_bits_be(Mode::Constant, 253, 0, 0, 0);
    }

    #[test]
    fn test_to_bits_be_public() {
        check_to_bits_be(Mode::Public, 0, 0, 253, 254);
    }

    #[test]
    fn test_to_bits_be_private() {
        check_to_bits_be(Mode::Private, 0, 0, 253, 254);
    }

    #[test]
    fn test_one() {
        /// Checks that the field element, when converted to little-endian bits, is well-formed.
        fn check_bits_le(candidate: BaseField<Circuit>) {
            for (i, bit) in candidate.to_bits_le().iter().enumerate() {
                match i == 0 {
                    true => assert!(bit.eject_value()),
                    false => assert!(!bit.eject_value()),
                }
            }
        }

        /// Checks that the field element, when converted to big-endian bits, is well-formed.
        fn check_bits_be(candidate: BaseField<Circuit>) {
            for (i, bit) in candidate.to_bits_be().iter().rev().enumerate() {
                match i == 0 {
                    true => assert!(bit.eject_value()),
                    false => assert!(!bit.eject_value()),
                }
            }
        }

        let one = <Circuit as Environment>::BaseField::one();

        // Constant
        check_bits_le(BaseField::<Circuit>::new(Mode::Constant, one));
        check_bits_be(BaseField::<Circuit>::new(Mode::Constant, one));
        // Public
        check_bits_le(BaseField::<Circuit>::new(Mode::Public, one));
        check_bits_be(BaseField::<Circuit>::new(Mode::Public, one));
        // Private
        check_bits_le(BaseField::<Circuit>::new(Mode::Private, one));
        check_bits_be(BaseField::<Circuit>::new(Mode::Private, one));
    }
}
