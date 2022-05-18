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

mod commit;
mod commit_uncompressed;
mod hash;
mod hash_uncompressed;

#[cfg(test)]
use snarkvm_circuits_environment::{assert_count, assert_output_mode, assert_scope};

use crate::algorithms::{Commit, CommitUncompressed, Hash, HashUncompressed};
use snarkvm_algorithms::crypto_hash::hash_to_curve;
use snarkvm_circuits_types::prelude::*;

/// Pedersen64 is an *additively-homomorphic* collision-resistant hash function that takes a 64-bit input.
pub type Pedersen64<E> = Pedersen<E, 1, 64>;
/// Pedersen128 is an *additively-homomorphic* collision-resistant hash function that takes a 128-bit input.
pub type Pedersen128<E> = Pedersen<E, 1, 128>;

/// Pedersen is a collision-resistant hash function that takes a variable-length input.
/// The Pedersen hash function does *not* behave like a random oracle, see Poseidon for one.
pub struct Pedersen<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> {
    /// The base windows for the Pedersen hash.
    bases: Vec<Vec<Group<E>>>,
    /// The random base window for the Pedersen commitment.
    random_base: Vec<Group<E>>,
}

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> Pedersen<E, NUM_WINDOWS, WINDOW_SIZE> {
    /// Initializes a new instance of Pedersen with the given setup message.
    pub fn setup(message: &str) -> Self {
        Self {
            bases: (0..NUM_WINDOWS)
                .map(|_| {
                    // Construct an indexed message to attempt to sample a base.
                    let (generator, _, _) = hash_to_curve(&format!("Aleo.Pedersen.Base.{message}"));
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
                let (generator, _, _) = hash_to_curve(&format!("Aleo.Pedersen.RandomBase.{message}"));
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
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_console::algorithms::Pedersen as NativePedersen;
    use snarkvm_curves::{AffineCurve, ProjectiveCurve};

    const ITERATIONS: u64 = 10;
    const MESSAGE: &str = "PedersenCircuit0";
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
            let native = NativePedersen::<Projective, WINDOW_SIZE>::setup(MESSAGE);

            Circuit::scope("Pedersen::setup", || {
                // Perform the setup operation.
                let circuit = Pedersen::<Circuit, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);
                assert_scope!(num_constants, num_public, num_private, num_constraints);

                // Check for equivalency of the bases.
                native.base_window().iter().zip_eq(circuit.bases.iter().flatten()).for_each(|(expected, candidate)| {
                    assert_eq!(expected.to_affine(), candidate.eject_value());
                });

                // Check for equality of the random base.
                native.random_base_window().iter().zip_eq(circuit.random_base.iter()).for_each(
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
        check_setup::<1, WINDOW_SIZE_MULTIPLIER>(785, 0, 0, 0);
        check_setup::<1, { 2 * WINDOW_SIZE_MULTIPLIER }>(809, 0, 0, 0);
        check_setup::<1, { 3 * WINDOW_SIZE_MULTIPLIER }>(833, 0, 0, 0);
        check_setup::<1, { 4 * WINDOW_SIZE_MULTIPLIER }>(857, 0, 0, 0);
        check_setup::<1, { 5 * WINDOW_SIZE_MULTIPLIER }>(881, 0, 0, 0);
    }
}
