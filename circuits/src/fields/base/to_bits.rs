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

        let bits = self
            .eject_value()
            .to_bits_le()
            .iter()
            .map(|bit| Boolean::new(mode, *bit))
            .collect::<Vec<_>>();

        let mut accumulator = BaseField::zero();
        let mut coefficient = BaseField::one();

        for bit in &bits {
            accumulator += BaseField::from(bit) * &coefficient;
            coefficient = coefficient.double();
        }

        // Ensure value * 1 == (2^i * b_i + ... + 2^0 * b_0)
        E::enforce(|| (*self, E::one(), accumulator));

        bits
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
    use crate::Circuit;
    use snarkvm_fields::PrimeField;
    use snarkvm_utilities::UniformRand;

    use itertools::Itertools;
    use rand::thread_rng;

    const ITERATIONS: usize = 100;

    #[test]
    fn test_to_bits_le() {
        let expected_number_of_bits = <<Circuit as Environment>::BaseField as PrimeField>::size_in_bits();

        // Constant
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());
            let candidate = BaseField::<Circuit>::new(Mode::Constant, expected);

            Circuit::scoped(&format!("Constant {}", i), |scope| {
                let candidate = candidate.to_bits_le();
                assert_eq!(expected_number_of_bits, candidate.len());
                for (expected_bit, candidate_bit) in expected.to_bits_le().iter().zip_eq(candidate.iter()) {
                    assert_eq!(*expected_bit, candidate_bit.eject_value());
                }

                assert_eq!(506, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(0, scope.num_private_in_scope());
                assert_eq!(0, scope.num_constraints_in_scope());
            });
        }

        // Public
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());
            let candidate = BaseField::<Circuit>::new(Mode::Public, expected);

            Circuit::scoped(&format!("Public {}", i), |scope| {
                let candidate = candidate.to_bits_le();
                assert_eq!(expected_number_of_bits, candidate.len());
                for (expected_bit, candidate_bit) in expected.to_bits_le().iter().zip_eq(candidate.iter()) {
                    assert_eq!(*expected_bit, candidate_bit.eject_value());
                }

                assert_eq!(0, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(253, scope.num_private_in_scope());
                assert_eq!(254, scope.num_constraints_in_scope());
            });
        }

        // Private
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());
            let candidate = BaseField::<Circuit>::new(Mode::Private, expected);

            Circuit::scoped(&format!("Private {}", i), |scope| {
                let candidate = candidate.to_bits_le();
                assert_eq!(expected_number_of_bits, candidate.len());
                for (expected_bit, candidate_bit) in expected.to_bits_le().iter().zip_eq(candidate.iter()) {
                    assert_eq!(*expected_bit, candidate_bit.eject_value());
                }

                assert_eq!(0, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(253, scope.num_private_in_scope());
                assert_eq!(254, scope.num_constraints_in_scope());
            });
        }
    }

    #[test]
    fn test_to_bits_be() {
        let expected_number_of_bits = <<Circuit as Environment>::BaseField as PrimeField>::size_in_bits();

        // Constant
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());
            let candidate = BaseField::<Circuit>::new(Mode::Constant, expected);

            Circuit::scoped(&format!("Constant {}", i), |scope| {
                let candidate = candidate.to_bits_be();
                assert_eq!(expected_number_of_bits, candidate.len());
                for (expected_bit, candidate_bit) in expected.to_bits_be().iter().zip_eq(candidate.iter()) {
                    assert_eq!(*expected_bit, candidate_bit.eject_value());
                }

                assert_eq!(506, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(0, scope.num_private_in_scope());
                assert_eq!(0, scope.num_constraints_in_scope());
            });
        }

        // Public
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());
            let candidate = BaseField::<Circuit>::new(Mode::Public, expected);

            Circuit::scoped(&format!("Public {}", i), |scope| {
                let candidate = candidate.to_bits_be();
                assert_eq!(expected_number_of_bits, candidate.len());
                for (expected_bit, candidate_bit) in expected.to_bits_be().iter().zip_eq(candidate.iter()) {
                    assert_eq!(*expected_bit, candidate_bit.eject_value());
                }

                assert_eq!(0, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(253, scope.num_private_in_scope());
                assert_eq!(254, scope.num_constraints_in_scope());
            });
        }

        // Private
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: <Circuit as Environment>::BaseField = UniformRand::rand(&mut thread_rng());
            let candidate = BaseField::<Circuit>::new(Mode::Private, expected);

            Circuit::scoped(&format!("Private {}", i), |scope| {
                let candidate = candidate.to_bits_be();
                assert_eq!(expected_number_of_bits, candidate.len());
                for (expected_bit, candidate_bit) in expected.to_bits_be().iter().zip_eq(candidate.iter()) {
                    assert_eq!(*expected_bit, candidate_bit.eject_value());
                }

                assert_eq!(0, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(253, scope.num_private_in_scope());
                assert_eq!(254, scope.num_constraints_in_scope());
            });
        }
    }

    #[test]
    fn test_one() {
        let one = <Circuit as Environment>::BaseField::one();

        /// Checks that the field element, when converted to little-endian bits, is well-formed.
        fn check_bits_le(candidate: BaseField<Circuit>) {
            for (i, bit) in candidate.to_bits_le().iter().enumerate() {
                match i == 0 {
                    true => assert_eq!(true, bit.eject_value()),
                    false => assert_eq!(false, bit.eject_value()),
                }
            }
        }

        /// Checks that the field element, when converted to big-endian bits, is well-formed.
        fn check_bits_be(candidate: BaseField<Circuit>) {
            for (i, bit) in candidate.to_bits_be().iter().rev().enumerate() {
                match i == 0 {
                    true => assert_eq!(true, bit.eject_value()),
                    false => assert_eq!(false, bit.eject_value()),
                }
            }
        }

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
