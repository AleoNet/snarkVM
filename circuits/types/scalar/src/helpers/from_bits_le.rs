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
use snarkvm_utilities::{FromBytes, ToBytes};

impl<E: Environment> FromBitsLE for Scalar<E> {
    type Boolean = Boolean<E>;

    /// Initializes a new scalar field element from a list of little-endian bits *without* trailing zeros.
    fn from_bits_le(bits_le: &[Self::Boolean]) -> Self {
        // Retrieve the data and scalar size.
        let size_in_data_bits = E::ScalarField::size_in_data_bits();
        let size_in_bits = E::ScalarField::size_in_bits();

        // Ensure the list of booleans is within the allowed size in bits.
        let num_bits = bits_le.len();
        if num_bits > size_in_bits {
            // Check if all excess bits are zero.
            let should_be_zero = bits_le[size_in_bits..].iter().fold(Boolean::constant(false), |acc, bit| acc | bit);
            // Ensure `should_be_zero` is zero.
            E::assert_eq(E::zero(), should_be_zero);
        }

        // Construct the sanitized list of bits, resizing up if necessary.
        let mut bits_le = bits_le.iter().take(size_in_bits).cloned().collect::<Vec<_>>();
        bits_le.resize(size_in_bits, Boolean::constant(false));

        // Construct the candidate scalar field element.
        let output = Scalar { bits_le };

        // If the number of bits is equivalent to the scalar size in bits,
        // ensure the scalar is below the scalar field modulus.
        if num_bits > size_in_data_bits {
            // Initialize the scalar field modulus as a constant base field variable.
            //
            // Note: We are reconstituting the scalar field into a base field here in order to check
            // that the scalar was synthesized correctly. This is safe as the scalar field modulus
            // is less that the base field modulus, and thus will always fit in a base field element.
            let modulus = Field::constant(match E::ScalarField::modulus().to_bytes_le() {
                Ok(modulus_bytes) => match E::BaseField::from_bytes_le(&modulus_bytes) {
                    Ok(modulus) => modulus,
                    Err(error) => E::halt(format!("Failed to load the scalar modulus as a constant: {error}")),
                },
                Err(error) => E::halt(format!("Failed to retrieve the scalar modulus as bytes: {error}")),
            });

            // Ensure `output` is less than `E::ScalarField::modulus()`.
            E::assert(output.to_field().is_less_than(&modulus));
        }

        output
    }
}

impl<E: Environment> Metadata<dyn FromBitsLE<Boolean = Boolean<E>>> for Scalar<E> {
    type Case = Vec<CircuitType<Boolean<E>>>;
    type OutputType = CircuitType<Self>;

    fn count(case: &Self::Case) -> Count {
        match case.iter().all(|bit| bit.is_constant()) {
            true => Count::is(507, 0, 0, 0),
            false => {
                let excess_constraints = case.len().saturating_sub(E::ScalarField::size_in_bits()) as u64;
                let excess_private = excess_constraints.saturating_sub(1);
                Count::is(254, 0, 769 + excess_private, 771 + excess_constraints)
            }
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case.eject_mode() {
            Mode::Constant => {
                let bits_le = case.into_iter().map(|bit| bit.circuit()).collect::<Vec<_>>();
                CircuitType::from(Self::from_bits_le(&bits_le))
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

    fn check_from_bits_le(mode: Mode) {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: <Circuit as Environment>::ScalarField = UniformRand::rand(&mut test_rng());
            let given_bits = Scalar::<Circuit>::new(mode, expected).to_bits_le();
            let expected_size_in_bits = given_bits.len();

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = Scalar::<Circuit>::from_bits_le(&given_bits);
                assert_eq!(expected, candidate.eject_value());
                assert_eq!(expected_size_in_bits, candidate.bits_le.len());

                let case = given_bits.iter().map(CircuitType::from).collect();
                assert_count!(Scalar<Circuit>, FromBitsLE<Boolean = Boolean<Circuit>>, &case);
                assert_output_type!(Scalar<Circuit>, FromBitsLE<Boolean = Boolean<Circuit>>, case, candidate);
            });

            // Add excess zero bits.
            let given_bits = vec![given_bits, vec![Boolean::new(mode, false); i as usize]].concat();

            Circuit::scope(&format!("Excess {} {}", mode, i), || {
                let candidate = Scalar::<Circuit>::from_bits_le(&given_bits);
                assert_eq!(expected, candidate.eject_value());
                assert_eq!(expected_size_in_bits, candidate.bits_le.len());

                let case = given_bits.iter().map(CircuitType::from).collect();
                assert_count!(Scalar<Circuit>, FromBitsLE<Boolean = Boolean<Circuit>>, &case);
                assert_output_type!(Scalar<Circuit>, FromBitsLE<Boolean = Boolean<Circuit>>, case, candidate);
            });
        }
    }

    #[test]
    fn test_from_bits_le_constant() {
        check_from_bits_le(Mode::Constant);
    }

    #[test]
    fn test_from_bits_le_public() {
        check_from_bits_le(Mode::Public);
    }

    #[test]
    fn test_from_bits_le_private() {
        check_from_bits_le(Mode::Private);
    }
}
