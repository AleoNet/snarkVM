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

mod hash;
mod hash_uncompressed;

#[cfg(test)]
use snarkvm_circuits_environment::assert_scope;

use crate::{Commit, CommitUncompressed, Hash, HashUncompressed};
use snarkvm_algorithms::crypto_hash::hash_to_curve;
use snarkvm_circuits_types::prelude::*;
use snarkvm_curves::{MontgomeryParameters, TwistedEdwardsParameters};
use snarkvm_utilities::BigInteger;

/// Sinsemilla is a collision-resistant hash function that takes a fixed-length input.
/// The Sinsemilla hash function does *not* behave like a random oracle, see Poseidon for one.
pub struct Sinsemilla<E: Environment, const WINDOW_SIZE: usize, const NUM_WINDOWS: usize> {
    q: Group<E>,
    p_lookups: Vec<Group<E>>,
}

impl<E: Environment, const WINDOW_SIZE: usize, const NUM_WINDOWS: usize> Sinsemilla<E, WINDOW_SIZE, NUM_WINDOWS> {
    /// Initializes a new instance of Sinsemilla with the given setup message.
    pub fn setup(message: &str) -> Self {
        // Calculate the maximum window size.
        let mut maximum_window_size = 0;
        let mut range = <E::ScalarField as PrimeField>::BigInteger::from(2_u64);
        while range < E::ScalarField::modulus_minus_one_div_two() {
            // range < (p-1)/2
            range.muln(1);
            maximum_window_size += 1;
        }
        assert!(WINDOW_SIZE <= maximum_window_size, "The maximum Sinsemilla window size is {maximum_window_size}");

        // Compute Q
        let (generator, _, _) = hash_to_curve(message);
        let q = Group::constant(generator);

        // Compute P[0..2^WINDOW_SIZE-1]
        let table_size = 2usize.pow(WINDOW_SIZE as u32);
        let mut p_lookups = Vec::with_capacity(table_size);
        for i in 0..table_size {
            let (generator, _, _) = hash_to_curve(&format!("{:?}", (i as u32).to_le_bytes()));
            let p = Group::constant(generator);
            p_lookups.push(p);
        }

        Self { q, p_lookups }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_algorithms::{crh::SinsemillaCRH, CRH};
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_curves::{AffineCurve, ProjectiveCurve};

    const ITERATIONS: u64 = 10;
    const MESSAGE: &str = "SinsemillaCircuit0";
    const WINDOW_SIZE_MULTIPLIER: usize = 8;

    type Projective = <<Circuit as Environment>::Affine as AffineCurve>::Projective;

    fn check_setup<const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>(
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        for _ in 0..ITERATIONS {
            // Initialize the native Pedersen hash.
            let native = SinsemillaCRH::<Projective, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);

            Circuit::scope("Sinsemilla::setup", || {
                // Perform the setup operation.
                let circuit = Sinsemilla::<Circuit, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);
                assert_scope!(num_constants, num_public, num_private, num_constraints);

                // Check for equivalency of the Q.
                assert_eq!(native.parameters().q.to_affine(), circuit.q.eject_value());

                // Check for equality of the lookup table.
                native.parameters().p_lookups.iter().zip_eq(circuit.p_lookups.iter()).for_each(
                    |(expected, candidate)| {
                        assert_eq!(expected.to_affine(), candidate.eject_value());
                    },
                );
            });
        }
    }

    #[test]
    fn test_setup_constant() {
        // Set the number of windows, and modulate the window size.
        check_setup::<10, 253>(4100, 0, 0, 0);
    }
}
