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

impl<E: Environment> ToBits for Group<E> {
    type Boolean = Boolean<E>;

    /// Outputs the little-endian bit representation of `self.x` *without* trailing zeros.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        (&self).to_bits_le()
    }

    /// Outputs the big-endian bit representation of `self.x` *without* leading zeros.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        (&self).to_bits_be()
    }
}

impl<E: Environment> ToBits for &Group<E> {
    type Boolean = Boolean<E>;

    /// Outputs the little-endian bit representation of `self.x` *without* trailing zeros.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        self.x.to_bits_le()
    }

    /// Outputs the big-endian bit representation of `self.x` *without* leading zeros.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        self.x.to_bits_be()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 100;

    fn check_to_bits_le(mode: Mode, num_constants: u64, num_public: u64, num_private: u64, num_constraints: u64) {
        let expected_number_of_bits = <<Circuit as Environment>::BaseField as PrimeField>::size_in_bits();

        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected = Uniform::rand(&mut test_rng());
            let candidate = Group::<Circuit>::new(mode, expected);

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = candidate.to_bits_le();
                assert_eq!(expected_number_of_bits, candidate.len());
                for (expected_bit, candidate_bit) in
                    expected.to_x_coordinate().to_bits_le().iter().zip_eq(candidate.iter())
                {
                    assert_eq!(*expected_bit, candidate_bit.eject_value());
                }
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    fn check_to_bits_be(mode: Mode, num_constants: u64, num_public: u64, num_private: u64, num_constraints: u64) {
        let expected_number_of_bits = <<Circuit as Environment>::BaseField as PrimeField>::size_in_bits();

        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected = Uniform::rand(&mut test_rng());
            let candidate = Group::<Circuit>::new(mode, expected);

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = candidate.to_bits_be();
                assert_eq!(expected_number_of_bits, candidate.len());
                for (expected_bit, candidate_bit) in
                    expected.to_x_coordinate().to_bits_be().iter().zip_eq(candidate.iter())
                {
                    assert_eq!(*expected_bit, candidate_bit.eject_value());
                }
                assert_scope!(num_constants, num_public, num_private, num_constraints);
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
}
