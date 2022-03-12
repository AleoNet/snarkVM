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

impl<E: Environment> ToField<E> for Scalar<E> {
    type Field = BaseField<E>;

    /// Casts a scalar field element into a base field element.
    fn to_field(&self) -> Self::Field {
        // Note: We are reconstituting the scalar field into a base field here in order to check
        // that the scalar was synthesized correctly. This is safe as the scalar field modulus
        // is less that the base field modulus, and thus will always fit in a base field element.
        debug_assert!(E::ScalarField::size_in_bits() < E::BaseField::size_in_bits());

        // Reconstruct the bits as a linear combination representing the original field value.
        let mut accumulator = BaseField::zero();
        let mut coefficient = BaseField::one();
        for bit in &self.bits_le {
            accumulator += BaseField::from(bit) * &coefficient;
            coefficient = coefficient.double();
        }

        accumulator
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_circuit, Circuit};
    use snarkvm_fields::PrimeField;
    use snarkvm_utilities::UniformRand;

    use itertools::Itertools;
    use rand::thread_rng;

    fn check_to_field(name: &str, expected: &[bool], candidate: &Scalar<Circuit>) {
        Circuit::scoped(name, || {
            // Perform the operation.
            let candidate = candidate.to_field();
            assert_circuit!(0, 0, 0, 0);

            // Extract the bits from the base field representation.
            let number_of_base_field_bits = <<Circuit as Environment>::BaseField as PrimeField>::size_in_bits();
            let candidate_bits_le = candidate.eject_value().to_bits_le();
            assert_eq!(number_of_base_field_bits, candidate_bits_le.len());

            // Ensure all scalar bits match with the expected result.
            let number_of_scalar_field_bits = <<Circuit as Environment>::ScalarField as PrimeField>::size_in_bits();
            for (expected_bit, candidate_bit) in
                expected.iter().zip_eq(&candidate_bits_le[0..number_of_scalar_field_bits])
            {
                assert_eq!(expected_bit, candidate_bit);
            }

            // Ensure all remaining bits are 0.
            for candidate_bit in &candidate_bits_le[number_of_scalar_field_bits..] {
                assert!(!candidate_bit);
            }
        });
        Circuit::reset();
    }

    #[test]
    fn test_to_field_constant() {
        let expected = UniformRand::rand(&mut thread_rng());
        let candidate = Scalar::<Circuit>::new(Mode::Constant, expected);
        check_to_field("Constant", &expected.to_bits_le(), &candidate);
    }

    #[test]
    fn test_to_field_public() {
        let expected = UniformRand::rand(&mut thread_rng());
        let candidate = Scalar::<Circuit>::new(Mode::Public, expected);
        check_to_field("Public", &expected.to_bits_le(), &candidate);
    }

    #[test]
    fn test_to_field_private() {
        let expected = UniformRand::rand(&mut thread_rng());
        let candidate = Scalar::<Circuit>::new(Mode::Private, expected);
        check_to_field("Private", &expected.to_bits_le(), &candidate);
    }

    #[test]
    fn test_one() {
        /// Checks that the `1` scalar field element, when converted to a base field, is well-formed.
        fn check_to_field_one(candidate: Scalar<Circuit>) {
            for (i, bit) in candidate.to_field().to_bits_le().iter().enumerate() {
                match i == 0 {
                    true => assert!(bit.eject_value()),
                    false => assert!(!bit.eject_value()),
                }
            }
        }

        let one = <Circuit as Environment>::ScalarField::one();

        // Constant
        check_to_field_one(Scalar::<Circuit>::new(Mode::Constant, one));
        // Public
        check_to_field_one(Scalar::<Circuit>::new(Mode::Public, one));
        // Private
        check_to_field_one(Scalar::<Circuit>::new(Mode::Private, one));
    }
}
