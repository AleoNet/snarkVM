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

impl<E: Environment> ToBits for Boolean<E> {
    type Boolean = Boolean<E>;

    /// Outputs `self` as a single-element vector.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        (&self).to_bits_le()
    }

    /// Outputs `self` as a single-element vector.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        (&self).to_bits_be()
    }
}

impl<E: Environment> ToBits for &Boolean<E> {
    type Boolean = Boolean<E>;

    /// Outputs `self` as a single-element vector.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        vec![(*self).clone()]
    }

    /// Outputs `self` as a single-element vector.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        vec![(*self).clone()]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    fn check_to_bits_le(name: &str, expected: &[bool], candidate: &Boolean<Circuit>) {
        Circuit::scope(name, || {
            let candidate = candidate.to_bits_le();
            assert_eq!(1, candidate.len());
            for (expected_bit, candidate_bit) in expected.iter().zip_eq(candidate.iter()) {
                assert_eq!(*expected_bit, candidate_bit.eject_value());
            }
            assert_scope!(0, 0, 0, 0);
        });
    }

    fn check_to_bits_be(name: &str, expected: &[bool], candidate: Boolean<Circuit>) {
        Circuit::scope(name, || {
            let candidate = candidate.to_bits_be();
            assert_eq!(1, candidate.len());
            for (expected_bit, candidate_bit) in expected.iter().zip_eq(candidate.iter()) {
                assert_eq!(*expected_bit, candidate_bit.eject_value());
            }
            assert_scope!(0, 0, 0, 0);
        });
    }

    #[test]
    fn test_to_bits_constant() {
        let candidate = Boolean::<Circuit>::new(Mode::Constant, true);
        check_to_bits_le("Constant", &[true], &candidate);
        check_to_bits_be("Constant", &[true], candidate);

        let candidate = Boolean::<Circuit>::new(Mode::Constant, false);
        check_to_bits_le("Constant", &[false], &candidate);
        check_to_bits_be("Constant", &[false], candidate);
    }

    #[test]
    fn test_to_bits_public() {
        let candidate = Boolean::<Circuit>::new(Mode::Public, true);
        check_to_bits_le("Public", &[true], &candidate);
        check_to_bits_be("Public", &[true], candidate);

        let candidate = Boolean::<Circuit>::new(Mode::Public, false);
        check_to_bits_le("Public", &[false], &candidate);
        check_to_bits_be("Public", &[false], candidate);
    }

    #[test]
    fn test_to_bits_private() {
        let candidate = Boolean::<Circuit>::new(Mode::Private, true);
        check_to_bits_le("Private", &[true], &candidate);
        check_to_bits_be("Private", &[true], candidate);

        let candidate = Boolean::<Circuit>::new(Mode::Private, false);
        check_to_bits_le("Private", &[false], &candidate);
        check_to_bits_be("Private", &[false], candidate);
    }
}
