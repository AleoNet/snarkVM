// Copyright 2024 Aleo Network Foundation
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:

// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

#[cfg(feature = "console")]
impl<A: Aleo> ToBits for ComputeKey<A> {
    type Boolean = Boolean<A>;

    /// Outputs the little-endian bit representation of the compute key *without* trailing zeros.
    fn write_bits_le(&self, vec: &mut Vec<Self::Boolean>) {
        (&self).write_bits_le(vec);
    }

    /// Outputs the big-endian bit representation of the compute key *without* leading zeros.
    fn write_bits_be(&self, vec: &mut Vec<Self::Boolean>) {
        (&self).write_bits_be(vec);
    }
}

#[cfg(feature = "console")]
impl<A: Aleo> ToBits for &ComputeKey<A> {
    type Boolean = Boolean<A>;

    /// Outputs the little-endian bit representation of the compute key *without* trailing zeros.
    fn write_bits_le(&self, vec: &mut Vec<Self::Boolean>) {
        // Write the `pk_sig` bits.
        self.pk_sig.write_bits_le(vec);
        // Write the `pr_sig` bits.
        self.pr_sig.write_bits_le(vec);
    }

    /// Outputs the big-endian bit representation of the compute key *without* leading zeros.
    fn write_bits_be(&self, vec: &mut Vec<Self::Boolean>) {
        // Write the `pk_sig` bits.
        self.pk_sig.write_bits_be(vec);
        // Write the `pr_sig` bits.
        self.pr_sig.write_bits_be(vec);
    }
}

#[cfg(all(test, feature = "console"))]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_circuit_network::AleoV0;
    use snarkvm_utilities::TestRng;

    type CurrentAleo = AleoV0;

    const ITERATIONS: u64 = 100;

    fn check_to_bits_le(mode: Mode, num_constants: u64, num_public: u64, num_private: u64, num_constraints: u64) {
        let expected_number_of_bits = console::ComputeKey::<<CurrentAleo as Environment>::Network>::size_in_bits();

        let rng = &mut TestRng::default();

        for i in 0..ITERATIONS {
            // Sample a random compute key.
            let expected = console::ComputeKey::try_from(console::PrivateKey::new(rng).unwrap()).unwrap();
            let candidate = ComputeKey::<CurrentAleo>::new(mode, expected);

            CurrentAleo::scope(format!("{mode} {i}"), || {
                let candidate = candidate.to_bits_le();
                assert_eq!(expected_number_of_bits, candidate.len());

                // Construct the expected bits.
                let mut expected_bits = Vec::new();
                expected_bits.extend(expected.pk_sig().to_bits_le());
                expected_bits.extend(expected.pr_sig().to_bits_le());

                for (expected_bit, candidate_bit) in expected_bits.iter().zip_eq(candidate.iter()) {
                    assert_eq!(*expected_bit, candidate_bit.eject_value());
                }
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    fn check_to_bits_be(mode: Mode, num_constants: u64, num_public: u64, num_private: u64, num_constraints: u64) {
        let expected_number_of_bits = console::ComputeKey::<<CurrentAleo as Environment>::Network>::size_in_bits();

        let rng = &mut TestRng::default();

        for i in 0..ITERATIONS {
            // Sample a random compute key.
            let expected = console::ComputeKey::try_from(console::PrivateKey::new(rng).unwrap()).unwrap();
            let candidate = ComputeKey::<CurrentAleo>::new(mode, expected);

            CurrentAleo::scope(format!("{mode} {i}"), || {
                let candidate = candidate.to_bits_be();
                assert_eq!(expected_number_of_bits, candidate.len());

                // Construct the expected bits.
                let mut expected_bits = Vec::new();
                expected_bits.extend(expected.pk_sig().to_bits_be());
                expected_bits.extend(expected.pr_sig().to_bits_be());

                for (expected_bit, candidate_bit) in expected_bits.iter().zip_eq(candidate.iter()) {
                    assert_eq!(*expected_bit, candidate_bit.eject_value());
                }
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    #[test]
    fn test_to_bits_le_constant() {
        check_to_bits_le(Mode::Constant, 506, 0, 0, 0);
    }

    #[test]
    fn test_to_bits_le_public() {
        check_to_bits_le(Mode::Public, 0, 0, 1010, 1014);
    }

    #[test]
    fn test_to_bits_le_private() {
        check_to_bits_le(Mode::Private, 0, 0, 1010, 1014);
    }

    #[test]
    fn test_to_bits_be_constant() {
        check_to_bits_be(Mode::Constant, 506, 0, 0, 0);
    }

    #[test]
    fn test_to_bits_be_public() {
        check_to_bits_be(Mode::Public, 0, 0, 1010, 1014);
    }

    #[test]
    fn test_to_bits_be_private() {
        check_to_bits_be(Mode::Private, 0, 0, 1010, 1014);
    }
}
