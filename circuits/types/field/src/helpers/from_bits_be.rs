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

impl<E: Environment> FromBitsBE for Field<E> {
    type Boolean = Boolean<E>;

    /// Initializes a new base field element from a list of big-endian bits *without* leading zeros.
    fn from_bits_be(bits_be: &[Self::Boolean]) -> Self {
        // Reverse the given bits from big-endian into little-endian.
        // Note: This is safe as the bit representation is consistent (there are no leading zeros).
        let mut bits_le = bits_be.to_vec();
        bits_le.reverse();

        Self::from_bits_le(&bits_le)
    }
}

impl<E: Environment> Metadata<dyn FromBitsBE<Boolean = Boolean<E>>> for Field<E> {
    type Case = CircuitType<Vec<Boolean<E>>>;
    type OutputType = CircuitType<Field<E>>;

    fn count(_modes: &Self::Case) -> Count {
        // TODO: Waiting for PR#711 to land as it significantly changes the counts.
        todo!()
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case {
            CircuitType::Constant(constant) => CircuitType::from(Field::from_bits_be(constant.circuit())),
            _ => CircuitType::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: u64 = 100;

    fn check_from_bits_le(mode: Mode, num_constants: u64, num_public: u64, num_private: u64, num_constraints: u64) {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            let given_bits = Field::<Circuit>::new(mode, expected).to_bits_le();
            let expected_size_in_bits = given_bits.len();

            Circuit::scope(format!("{mode} {i}"), || {
                let candidate = Field::<Circuit>::from_bits_le(&given_bits);
                assert_eq!(expected, candidate.eject_value());
                assert_eq!(expected_size_in_bits, candidate.bits_le.get().expect("Caching failed").len());
                assert_scope!(num_constants, num_public, num_private, num_constraints);

                // Ensure a subsequent call to `to_bits_le` does not incur additional costs.
                let candidate_bits = candidate.to_bits_le();
                assert_eq!(expected_size_in_bits, candidate_bits.len());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });

            // Add excess zero bits.
            let candidate = vec![given_bits, vec![Boolean::new(mode, false); i as usize]].concat();

            Circuit::scope(&format!("Excess {} {}", mode, i), || {
                let candidate = Field::<Circuit>::from_bits_le(&candidate);
                assert_eq!(expected, candidate.eject_value());
                assert_eq!(expected_size_in_bits, candidate.bits_le.get().expect("Caching failed").len());
                match mode.is_constant() {
                    true => assert_scope!(num_constants, num_public, num_private, num_constraints),
                    // `num_private` gets 1 free excess bit, then is incremented by one for each excess bit.
                    // `num_constraints` is incremented by one for each excess bit.
                    false => {
                        assert_scope!(num_constants, num_public, num_private + i.saturating_sub(1), num_constraints + i)
                    }
                };
            });
        }
    }

    fn check_from_bits_be(mode: Mode, num_constants: u64, num_public: u64, num_private: u64, num_constraints: u64) {
        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected: <Circuit as Environment>::BaseField = UniformRand::rand(&mut test_rng());
            let given_bits = Field::<Circuit>::new(mode, expected).to_bits_be();
            let expected_size_in_bits = given_bits.len();

            Circuit::scope(format!("{mode} {i}"), || {
                let candidate = Field::<Circuit>::from_bits_be(&given_bits);
                assert_eq!(expected, candidate.eject_value());
                assert_eq!(expected_size_in_bits, candidate.bits_le.get().expect("Caching failed").len());
                assert_scope!(num_constants, num_public, num_private, num_constraints);

                // Ensure a subsequent call to `to_bits_be` does not incur additional costs.
                let candidate_bits = candidate.to_bits_be();
                assert_eq!(expected_size_in_bits, candidate_bits.len());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });

            // Add excess zero bits.
            let candidate = vec![vec![Boolean::new(mode, false); i as usize], given_bits].concat();

            Circuit::scope(&format!("Excess {} {}", mode, i), || {
                let candidate = Field::<Circuit>::from_bits_be(&candidate);
                assert_eq!(expected, candidate.eject_value());
                assert_eq!(expected_size_in_bits, candidate.bits_le.get().expect("Caching failed").len());
                match mode.is_constant() {
                    true => assert_scope!(num_constants, num_public, num_private, num_constraints),
                    // `num_private` gets 1 free excess bit, then is incremented by one for each excess bit.
                    // `num_constraints` is incremented by one for each excess bit.
                    false => {
                        assert_scope!(num_constants, num_public, num_private + i.saturating_sub(1), num_constraints + i)
                    }
                };
            });
        }
    }

    #[test]
    fn test_from_bits_le_constant() {
        check_from_bits_le(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_le_public() {
        check_from_bits_le(Mode::Public, 0, 0, 252, 418);
    }

    #[test]
    fn test_from_bits_le_private() {
        check_from_bits_le(Mode::Private, 0, 0, 252, 418);
    }

    #[test]
    fn test_from_bits_be_constant() {
        check_from_bits_be(Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_from_bits_be_public() {
        check_from_bits_be(Mode::Public, 0, 0, 252, 418);
    }

    #[test]
    fn test_from_bits_be_private() {
        check_from_bits_be(Mode::Private, 0, 0, 252, 418);
    }
}
