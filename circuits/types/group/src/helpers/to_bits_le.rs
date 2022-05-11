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

// TODO: Split into multiple Traits for coherence with Metadata

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

impl<E: Environment> Metadata<dyn ToBits<Boolean = Boolean<E>>> for Group<E> {
    type Case = CircuitType<Self>;
    type OutputType = CircuitType<Vec<Boolean<E>>>;

    fn count(case: &Self::Case) -> Count {
        match case {
            CircuitType::Constant(_) => Count::is(253, 0, 0, 0),
            _ => Count::is(0, 0, 253, 254),
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case {
            CircuitType::Constant(_) => CircuitType::from(case.circuit().to_bits_le()),
            _ => CircuitType::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, ToBits as TBits, UniformRand};

    const ITERATIONS: u64 = 100;

    fn check_to_bits_le(mode: Mode) {
        let expected_number_of_bits = <<Circuit as Environment>::BaseField as PrimeField>::size_in_bits();

        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
            let candidate = Group::<Circuit>::new(mode, expected);

            Circuit::scope(&format!("{} {}", mode, i), || {
                let result = candidate.to_bits_le();
                assert_eq!(expected_number_of_bits, result.len());
                for (expected_bit, candidate_bit) in
                    expected.to_x_coordinate().to_bits_le().iter().zip_eq(result.iter())
                {
                    assert_eq!(*expected_bit, candidate_bit.eject_value());
                }

                let case = CircuitType::from(&candidate);
                assert_count!(ToBits<Boolean>() => Group, &case);
                assert_output_type!(ToBits<Boolean>() => Group, case, result);
            });
        }
    }

    fn check_to_bits_be(mode: Mode) {
        let expected_number_of_bits = <<Circuit as Environment>::BaseField as PrimeField>::size_in_bits();

        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: <Circuit as Environment>::Affine = UniformRand::rand(&mut test_rng());
            let candidate = Group::<Circuit>::new(mode, expected);

            Circuit::scope(&format!("{} {}", mode, i), || {
                let result = candidate.to_bits_be();
                assert_eq!(expected_number_of_bits, result.len());
                for (expected_bit, candidate_bit) in
                    expected.to_x_coordinate().to_bits_be().iter().zip_eq(result.iter())
                {
                    assert_eq!(*expected_bit, candidate_bit.eject_value());
                }

                let case = CircuitType::from(&candidate);
                assert_count!(ToBits<Boolean>() => Group, &case);
                assert_output_type!(ToBits<Boolean>() => Group, case, result);
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
}
