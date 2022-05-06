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

// TODO: Split into separate traits for coherence with metadata.

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
        self.bits_le.clone()
    }

    /// Outputs the big-endian bit representation of `self` *without* leading zeros.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        let mut bits_le = self.to_bits_le();
        bits_le.reverse();
        bits_le
    }
}

impl<E: Environment> Metadata<dyn ToBits<Boolean = Boolean<E>>> for Scalar<E> {
    type Case = CircuitType<Self>;
    type OutputType = CircuitType<Vec<Boolean<E>>>;

    fn count(_case: &Self::Case) -> Count {
        Count::is(0, 0, 0, 0)
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case {
            CircuitType::Constant(_) => CircuitType::from(case.circuit().to_bits_le()),
            CircuitType::Public => CircuitType::Public,
            CircuitType::Private => CircuitType::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    fn check_to_bits_le(name: &str, expected: &[bool], candidate: &Scalar<Circuit>) {
        let expected_number_of_bits = <<Circuit as Environment>::ScalarField as PrimeField>::size_in_bits();

        Circuit::scope(name, || {
            let result = candidate.to_bits_le();
            assert_eq!(expected_number_of_bits, result.len());
            for (expected_bit, candidate_bit) in expected.iter().zip_eq(result.iter()) {
                assert_eq!(*expected_bit, candidate_bit.eject_value());
            }

            let case = CircuitType::from(candidate);
            assert_count!(ToBits<Boolean>() => Scalar, &case);
            assert_output_type!(ToBits<Boolean>() => Scalar, case, result);
        });
    }

    fn check_to_bits_be(name: &str, expected: &[bool], candidate: Scalar<Circuit>) {
        let expected_number_of_bits = <<Circuit as Environment>::ScalarField as PrimeField>::size_in_bits();

        Circuit::scope(name, || {
            let result = candidate.to_bits_be();
            assert_eq!(expected_number_of_bits, result.len());
            for (expected_bit, candidate_bit) in expected.iter().zip_eq(result.iter()) {
                assert_eq!(*expected_bit, candidate_bit.eject_value());
            }

            let case = CircuitType::from(candidate);
            assert_count!(ToBits<Boolean>() => Scalar, &case);
            assert_output_type!(ToBits<Boolean>() => Scalar, case, result);
        });
    }

    #[test]
    fn test_to_bits_constant() {
        let expected = UniformRand::rand(&mut test_rng());
        let candidate = Scalar::<Circuit>::new(Mode::Constant, expected);
        check_to_bits_le("Constant", &expected.to_bits_le(), &candidate);
        check_to_bits_be("Constant", &expected.to_bits_be(), candidate);
    }

    #[test]
    fn test_to_bits_public() {
        let expected = UniformRand::rand(&mut test_rng());
        let candidate = Scalar::<Circuit>::new(Mode::Public, expected);
        check_to_bits_le("Public", &expected.to_bits_le(), &candidate);
        check_to_bits_be("Public", &expected.to_bits_be(), candidate);
    }

    #[test]
    fn test_to_bits_private() {
        let expected = UniformRand::rand(&mut test_rng());
        let candidate = Scalar::<Circuit>::new(Mode::Private, expected);
        check_to_bits_le("Private", &expected.to_bits_le(), &candidate);
        check_to_bits_be("Private", &expected.to_bits_be(), candidate);
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

        let one = <Circuit as Environment>::ScalarField::one();

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
