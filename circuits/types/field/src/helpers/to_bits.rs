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

// TODO: Split into ToBitsLE and ToBitsBE so that Metadata is coherent.
impl<E: Environment> ToBits for Field<E> {
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

impl<E: Environment> ToBits for &Field<E> {
    type Boolean = Boolean<E>;

    /// Outputs the little-endian bit representation of `self` *without* trailing zeros.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        self.bits_le
            .get_or_init(|| {
                // Construct a vector of `Boolean`s comprising the bits of the field value.
                let bits_le = witness!(|self| self.to_bits_le());

                // Reconstruct the bits as a linear combination representing the original field value.
                let mut accumulator = Field::zero();
                let mut coefficient = Field::one();
                for bit in &bits_le {
                    accumulator += Field::from_boolean(bit) * &coefficient;
                    coefficient = coefficient.double();
                }

                // Ensure value * 1 == (2^i * b_i + ... + 2^0 * b_0)
                E::assert_eq(*self, accumulator);

                bits_le
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

impl<E: Environment> Metadata<dyn ToBits<Boolean = Boolean<E>>> for Field<E> {
    type Case = CircuitType<Field<E>>;
    type OutputType = CircuitType<Vec<Boolean<E>>>;

    fn count(case: &Self::Case) -> Count {
        match case.is_constant() {
            true => Count::is(253, 0, 0, 0),
            false => Count::is(0, 0, 253, 254),
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case.is_constant() {
            true => CircuitType::from(case.circuit().to_bits_le()),
            false => CircuitType::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: u64 = 100;

    fn check_to_bits_le(mode: Mode) {
        let expected_number_of_bits = <<Circuit as Environment>::BaseField as PrimeField>::size_in_bits();

        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            let candidate = Field::<Circuit>::new(mode, expected);

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate_bits = candidate.to_bits_le();
                assert_eq!(expected_number_of_bits, candidate_bits.len());
                for (expected_bit, candidate_bit) in expected.to_bits_le().iter().zip_eq(&candidate_bits) {
                    assert_eq!(*expected_bit, candidate_bit.eject_value());
                }

                let case = CircuitType::from(&candidate);
                assert_count!(ToBits<Boolean>() => Field, &case);
                assert_output_type!(ToBits<Boolean>() => Field, case, candidate_bits);

                // Ensure a second call to `to_bits_le` does not incur additional costs.
                let candidate_bits = candidate.to_bits_le();
                assert_eq!(expected_number_of_bits, candidate_bits.len());

                let case = CircuitType::from(&candidate);
                assert_count!(ToBits<Boolean>() => Field, &case);
                assert_output_type!(ToBits<Boolean>() => Field, case, candidate_bits);
            });
        }
    }

    fn check_to_bits_be(mode: Mode) {
        let expected_number_of_bits = <<Circuit as Environment>::BaseField as PrimeField>::size_in_bits();

        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            let candidate = Field::<Circuit>::new(mode, expected);

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate_bits = candidate.to_bits_be();
                assert_eq!(expected_number_of_bits, candidate_bits.len());
                for (expected_bit, candidate_bit) in expected.to_bits_be().iter().zip_eq(&candidate_bits) {
                    assert_eq!(*expected_bit, candidate_bit.eject_value());
                }

                let case = CircuitType::from(&candidate);
                assert_count!(ToBits<Boolean>() => Field, &case);
                assert_output_type!(ToBits<Boolean>() => Field, case, candidate_bits);

                // Ensure a second call to `to_bits_be` does not incur additional costs.
                let candidate_bits = candidate.to_bits_be();
                assert_eq!(expected_number_of_bits, candidate_bits.len());

                let case = CircuitType::from(candidate);
                assert_count!(ToBits<Boolean>() => Field, &case);
                assert_output_type!(ToBits<Boolean>() => Field, case, candidate_bits);
            });
        }
    }

    #[test]
    fn test_to_bits_le_constant() {
        check_to_bits_le(Mode::Constant);
    }

    #[test]
    fn test_to_bits_le_public() {
        check_to_bits_le(Mode::Public);
    }

    #[test]
    fn test_to_bits_le_private() {
        check_to_bits_le(Mode::Private);
    }

    #[test]
    fn test_to_bits_be_constant() {
        check_to_bits_be(Mode::Constant);
    }

    #[test]
    fn test_to_bits_be_public() {
        check_to_bits_be(Mode::Public);
    }

    #[test]
    fn test_to_bits_be_private() {
        check_to_bits_be(Mode::Private);
    }

    #[test]
    fn test_one() {
        /// Checks that the field element, when converted to little-endian bits, is well-formed.
        fn check_bits_le(candidate: Field<Circuit>) {
            for (i, bit) in candidate.to_bits_le().iter().enumerate() {
                match i == 0 {
                    true => assert!(bit.eject_value()),
                    false => assert!(!bit.eject_value()),
                }
            }
        }

        /// Checks that the field element, when converted to big-endian bits, is well-formed.
        fn check_bits_be(candidate: Field<Circuit>) {
            for (i, bit) in candidate.to_bits_be().iter().rev().enumerate() {
                match i == 0 {
                    true => assert!(bit.eject_value()),
                    false => assert!(!bit.eject_value()),
                }
            }
        }

        let one = <Circuit as Environment>::BaseField::one();

        // Constant
        check_bits_le(Field::<Circuit>::new(Mode::Constant, one));
        check_bits_be(Field::<Circuit>::new(Mode::Constant, one));
        // Public
        check_bits_le(Field::<Circuit>::new(Mode::Public, one));
        check_bits_be(Field::<Circuit>::new(Mode::Public, one));
        // Private
        check_bits_le(Field::<Circuit>::new(Mode::Private, one));
        check_bits_be(Field::<Circuit>::new(Mode::Private, one));
    }
}
