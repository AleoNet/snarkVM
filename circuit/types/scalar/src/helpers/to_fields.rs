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
use snarkvm_circuit_types_field::Field;

impl<E: Environment> ToFields for Scalar<E> {
    type Field = Field<E>;

    /// Casts a string into a list of base fields.
    fn to_fields(&self) -> Vec<Self::Field> {
        vec![self.to_field()]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    fn check_to_fields(name: &str, expected: &[bool], candidate: &Scalar<Circuit>) {
        Circuit::scope(name, || {
            // Perform the operation.
            let fields = candidate.to_fields();
            assert_eq!(1, fields.len());
            assert_scope!(0, 0, 0, 0);

            // Extract the bits from the base field representation.
            let number_of_base_field_bits = <<Circuit as Environment>::BaseField as PrimeField>::size_in_bits();
            let candidate_bits_le = fields[0].eject_value().to_bits_le();
            assert_eq!(number_of_base_field_bits, candidate_bits_le.len());

            // Ensure all scalar bits match with the expected result.
            let number_of_scalar_field_bits = console::Scalar::<<Circuit as Environment>::Network>::size_in_bits();
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
    fn test_to_fields_constant() {
        let expected = Uniform::rand(&mut test_rng());
        let candidate = Scalar::<Circuit>::new(Mode::Constant, expected);
        check_to_fields("Constant", &expected.to_bits_le(), &candidate);
    }

    #[test]
    fn test_to_fields_public() {
        let expected = Uniform::rand(&mut test_rng());
        let candidate = Scalar::<Circuit>::new(Mode::Public, expected);
        check_to_fields("Public", &expected.to_bits_le(), &candidate);
    }

    #[test]
    fn test_to_fields_private() {
        let expected = Uniform::rand(&mut test_rng());
        let candidate = Scalar::<Circuit>::new(Mode::Private, expected);
        check_to_fields("Private", &expected.to_bits_le(), &candidate);
    }

    #[test]
    fn test_one() {
        /// Checks that the `1` scalar field element, when converted to a base field, is well-formed.
        fn check_to_fields_one(candidate: Scalar<Circuit>) {
            let fields = candidate.to_fields();
            assert_eq!(1, fields.len());

            for (i, bit) in fields[0].to_bits_le().iter().enumerate() {
                match i == 0 {
                    true => assert!(bit.eject_value()),
                    false => assert!(!bit.eject_value()),
                }
            }
        }

        let one = console::Scalar::<<Circuit as Environment>::Network>::one();

        // Constant
        check_to_fields_one(Scalar::<Circuit>::new(Mode::Constant, one));
        // Public
        check_to_fields_one(Scalar::<Circuit>::new(Mode::Public, one));
        // Private
        check_to_fields_one(Scalar::<Circuit>::new(Mode::Private, one));
    }
}
