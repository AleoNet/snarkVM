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

impl<E: Environment> ToFields for StringType<E> {
    type Field = Field<E>;

    /// Casts a string into a list of base fields.
    fn to_fields(&self) -> Vec<Self::Field> {
        // Convert the string bytes into bits, then chunk them into lists of size
        // `E::BaseField::size_in_data_bits()` and recover the base field element for each chunk.
        // (For advanced users: Chunk into CAPACITY bits and create a linear combination per chunk.)
        self.to_bits_le().chunks(E::BaseField::size_in_data_bits()).map(Field::from_bits_le).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;
    use snarkvm_utilities::{bytes_from_bits_le, FromBytes};

    use rand::Rng;

    fn native_string_to_fields(string: &str) -> Vec<console::Field<<Circuit as Environment>::Network>> {
        string
            .to_string()
            .to_bits_le()
            .chunks(<Circuit as Environment>::BaseField::size_in_data_bits())
            .map(|chunk| {
                // Resize the list to match the field size in bits.
                let mut chunk = chunk.to_vec();
                chunk.resize(<Circuit as Environment>::BaseField::size_in_bits(), false);
                // Recover the field element.
                let chunk = bytes_from_bits_le(&chunk);
                console::Field::new(<Circuit as Environment>::BaseField::from_bytes_le(&chunk).unwrap())
            })
            .collect()
    }

    fn check_to_fields(
        name: &str,
        expected: &[console::Field<<Circuit as Environment>::Network>],
        candidate: &StringType<Circuit>,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        Circuit::scope(name, || {
            // Perform the operation.
            let candidate = candidate.to_fields();
            assert_eq!(expected.len(), candidate.len());
            assert_scope!(num_constants, num_public, num_private, num_constraints);

            // Ensure all field elements match with the expected result.
            for (expected_field, candidate_field) in expected.iter().zip_eq(&candidate) {
                assert_eq!(expected_field, &candidate_field.eject_value());
            }
        });
        Circuit::reset();
    }

    #[test]
    fn test_to_fields_constant() {
        let rng = &mut test_rng();

        // Sample a random string. Take 1/4th to ensure we fit for all code points.
        let given: String = (0..Circuit::NUM_STRING_BYTES / 4).map(|_| rng.gen::<char>()).collect();

        let expected = native_string_to_fields(&given);
        let candidate = StringType::<Circuit>::new(Mode::Constant, console::StringType::new(&given));
        check_to_fields("Constant", &expected, &candidate, 0, 0, 0, 0);
    }

    #[test]
    fn test_to_fields_public() {
        let rng = &mut test_rng();

        // Sample a random string. Take 1/4th to ensure we fit for all code points.
        let given: String = (0..Circuit::NUM_STRING_BYTES / 4).map(|_| rng.gen::<char>()).collect();

        let expected = native_string_to_fields(&given);
        let candidate = StringType::<Circuit>::new(Mode::Public, console::StringType::new(&given));
        check_to_fields("Public", &expected, &candidate, 0, 0, 0, 0);
    }

    #[test]
    fn test_to_fields_private() {
        let rng = &mut test_rng();

        // Sample a random string. Take 1/4th to ensure we fit for all code points.
        let given: String = (0..Circuit::NUM_STRING_BYTES / 4).map(|_| rng.gen::<char>()).collect();

        let expected = native_string_to_fields(&given);
        let candidate = StringType::<Circuit>::new(Mode::Private, console::StringType::new(&given));
        check_to_fields("Private", &expected, &candidate, 0, 0, 0, 0);
    }
}
