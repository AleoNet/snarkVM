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

mod commitment;
pub use commitment::*;
mod hash;
mod hash_uncompressed;

#[cfg(test)]
use snarkvm_circuits_environment::{assert_count, assert_output_mode, assert_scope};

use crate::{CommitmentScheme, Hash, HashUncompressed};
use snarkvm_algorithms::crypto_hash::hash_to_curve;
use snarkvm_circuits_types::prelude::*;

/// Pedersen64 is an *additively-homomorphic* collision-resistant hash function that takes a 64-bit input.
pub type Pedersen64<E> = Pedersen<E, 1, 64>;
/// Pedersen128 is an *additively-homomorphic* collision-resistant hash function that takes a 128-bit input.
pub type Pedersen128<E> = Pedersen<E, 1, 128>;
/// Pedersen256 is a collision-resistant hash function that takes a 256-bit input.
pub type Pedersen256<E> = Pedersen<E, 2, 128>;
/// Pedersen512 is a collision-resistant hash function that takes a 512-bit input.
pub type Pedersen512<E> = Pedersen<E, 4, 128>;
/// Pedersen1024 is a collision-resistant hash function that takes a 1024-bit input.
pub type Pedersen1024<E> = Pedersen<E, 8, 128>;

/// Pedersen is a collision-resistant hash function that takes a variable-length input.
/// The Pedersen hash function does *not* behave like a random oracle, see Poseidon for one.
pub struct Pedersen<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> {
    /// The base windows for the Pedersen hash.
    bases: Vec<Vec<Group<E>>>,
    /// A vector of random bases, used for computing the commitment.
    random_base: Vec<Group<E>>,
}

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> Pedersen<E, NUM_WINDOWS, WINDOW_SIZE> {
    /// Initializes a new instance of Pedersen with the given setup message.
    pub fn setup(message: &str) -> Self {
        Self {
            bases: (0..NUM_WINDOWS)
                .map(|index| {
                    // Construct an indexed message to attempt to sample a base.
                    let (generator, _, _) = hash_to_curve(&format!("{message} at {index}"));
                    // Inject the new base.
                    let mut base = Group::constant(generator);
                    // Construct the window with the base.
                    let mut powers = Vec::with_capacity(WINDOW_SIZE);
                    for _ in 0..WINDOW_SIZE {
                        powers.push(base.clone());
                        base = base.double();
                    }
                    powers
                })
                .collect(),
            random_base: {
                // Compute the random base
                let (generator, _, _) = hash_to_curve(&format!("{message} for random base"));
                let mut base = Group::constant(generator);

                let num_scalar_bits = E::ScalarField::size_in_bits();
                let mut random_base = Vec::with_capacity(num_scalar_bits);
                for _ in 0..num_scalar_bits {
                    random_base.push(base.clone());
                    base = base.double();
                }
                random_base
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_algorithms::{commitment::PedersenCommitment, CommitmentScheme, CRH};
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_curves::{AffineCurve, ProjectiveCurve};

    const ITERATIONS: usize = 10;
    const MESSAGE: &str = "PedersenCircuit0";
    const WINDOW_SIZE_MULTIPLIER: usize = 8;

    type Projective = <<Circuit as Environment>::Affine as AffineCurve>::Projective;

    fn check_setup<const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>(
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for _ in 0..ITERATIONS {
            // Initialize the native Pedersen hash.
            let native = PedersenCommitment::<Projective, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);

            Circuit::scope("Pedersen::setup", || {
                // Perform the setup operation.
                let circuit = Pedersen::<Circuit, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);
                assert_scope!(num_constants, num_public, num_private, num_constraints);

                // Check for equivalency of the bases.
                native.crh.parameters().iter().flatten().zip_eq(circuit.bases.iter().flatten()).for_each(
                    |(expected, candidate)| {
                        assert_eq!(expected.to_affine(), candidate.eject_value());
                    },
                );

                // Check for equality of the random base.
                native.random_base.iter().zip_eq(circuit.random_base.iter()).for_each(|(expected, candidate)| {
                    assert_eq!(expected.to_affine(), candidate.eject_value());
                });
            });
        }
    }

    #[test]
    fn test_setup_constant() {
        // Set the number of windows, and modulate the window size.
        check_setup::<1, WINDOW_SIZE_MULTIPLIER>(785, 0, 0, 0);
        check_setup::<1, { 2 * WINDOW_SIZE_MULTIPLIER }>(809, 0, 0, 0);
        check_setup::<1, { 3 * WINDOW_SIZE_MULTIPLIER }>(833, 0, 0, 0);
        check_setup::<1, { 4 * WINDOW_SIZE_MULTIPLIER }>(857, 0, 0, 0);
        check_setup::<1, { 5 * WINDOW_SIZE_MULTIPLIER }>(881, 0, 0, 0);

        // Set the window size, and modulate the number of windows.
        check_setup::<1, WINDOW_SIZE_MULTIPLIER>(785, 0, 0, 0);
        check_setup::<2, WINDOW_SIZE_MULTIPLIER>(813, 0, 0, 0);
        check_setup::<3, WINDOW_SIZE_MULTIPLIER>(841, 0, 0, 0);
        check_setup::<4, WINDOW_SIZE_MULTIPLIER>(869, 0, 0, 0);
        check_setup::<5, WINDOW_SIZE_MULTIPLIER>(897, 0, 0, 0);
    }
}
