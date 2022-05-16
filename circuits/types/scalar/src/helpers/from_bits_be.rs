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

impl<E: Environment> FromBitsBE for Scalar<E> {
    type Boolean = Boolean<E>;

    /// Initializes a new scalar field element from a list of big-endian bits *without* leading zeros.
    fn from_bits_be(bits_be: &[Self::Boolean]) -> Self {
        // Reverse the given bits from big-endian into little-endian.
        // Note: This is safe as the bit representation is consistent (there are no leading zeros).
        let mut bits_le = bits_be.to_vec();
        bits_le.reverse();

        Self::from_bits_le(&bits_le)
    }
}

impl<E: Environment> Metadata<dyn FromBitsBE<Boolean = Boolean<E>>> for Scalar<E> {
    type Case = Vec<CircuitType<Boolean<E>>>;
    type OutputType = CircuitType<Self>;

    fn count(case: &Self::Case) -> Count {
        count!(Self, FromBitsLE<Boolean = Boolean<E>>, case)
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case.eject_mode() {
            Mode::Constant => {
                let bits_be = case.into_iter().map(|bit| bit.circuit()).collect::<Vec<_>>();
                CircuitType::from(Self::from_bits_be(&bits_be))
            }
            Mode::Public => CircuitType::Public,
            Mode::Private => CircuitType::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: u64 = 100;

    fn check_from_bits_be(mode: Mode) {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut test_rng());
            let given_bits = Scalar::<Circuit>::new(mode, expected).to_bits_be();
            let expected_size_in_bits = given_bits.len();

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = Scalar::<Circuit>::from_bits_be(&given_bits);
                assert_eq!(expected, candidate.eject_value());
                assert_eq!(expected_size_in_bits, candidate.bits_le.len());

                let case = given_bits.iter().map(CircuitType::from).collect();
                assert_count!(Scalar<Circuit>, FromBitsBE<Boolean = Boolean<Circuit>>, &case);
                assert_output_type!(Scalar<Circuit>, FromBitsBE<Boolean = Boolean<Circuit>>, case, candidate);
            });

            // Add excess zero bits.
            let given_bits = vec![vec![Boolean::new(mode, false); i as usize], given_bits].concat();

            Circuit::scope(&format!("Excess {} {}", mode, i), || {
                let candidate = Scalar::<Circuit>::from_bits_be(&given_bits);
                assert_eq!(expected, candidate.eject_value());
                assert_eq!(expected_size_in_bits, candidate.bits_le.len());

                let case = given_bits.into_iter().map(CircuitType::from).collect();
                assert_count!(Scalar<Circuit>, FromBitsBE<Boolean = Boolean<Circuit>>, &case);
                assert_output_type!(Scalar<Circuit>, FromBitsBE<Boolean = Boolean<Circuit>>, case, candidate);
            });
        }
    }

    #[test]
    fn test_from_bits_be_constant() {
        check_from_bits_be(Mode::Constant);
    }

    #[test]
    fn test_from_bits_be_public() {
        check_from_bits_be(Mode::Public);
    }

    #[test]
    fn test_from_bits_be_private() {
        check_from_bits_be(Mode::Private);
    }
}
