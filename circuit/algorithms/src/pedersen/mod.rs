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

#[cfg(all(test, console))]
use snarkvm_circuit_environment::{assert_count, assert_output_mode, assert_scope};

use crate::{Commit, CommitUncompressed, Hash, HashUncompressed};
use snarkvm_circuit_types::prelude::*;

/// Pedersen64 is an *additively-homomorphic* collision-resistant hash function that takes a 64-bit input.
pub type Pedersen64<E> = Pedersen<E, 64>;
/// Pedersen128 is an *additively-homomorphic* collision-resistant hash function that takes a 128-bit input.
pub type Pedersen128<E> = Pedersen<E, 128>;

/// Pedersen is a collision-resistant hash function that takes a variable-length input.
/// The Pedersen hash function does *not* behave like a random oracle, see Poseidon for one.
pub struct Pedersen<E: Environment, const NUM_BITS: u8> {
    /// The base window for the Pedersen hash.
    base_window: Vec<Group<E>>,
    /// The random base window for the Pedersen commitment.
    random_base: Vec<Group<E>>,
}

#[cfg(console)]
impl<E: Environment, const NUM_BITS: u8> Pedersen<E, NUM_BITS> {
    /// Initializes a new instance of Pedersen with the given setup message.
    pub fn setup(message: &str) -> Self {
        // Construct an indexed message to attempt to sample a base.
        let (generator, _, _) = console::Blake2Xs::hash_to_curve(&format!("Aleo.Pedersen.Base.{message}"));
        // Inject the new base.
        let mut base = Group::constant(generator);
        // Construct the window with the base.
        let mut base_window = Vec::with_capacity(NUM_BITS as usize);
        for _ in 0..NUM_BITS {
            base_window.push(base.clone());
            base = base.double();
        }

        // Compute the random base.
        let (generator, _, _) = console::Blake2Xs::hash_to_curve(&format!("Aleo.Pedersen.RandomBase.{message}"));
        let mut base = Group::constant(generator);

        let num_scalar_bits = E::ScalarField::size_in_bits();
        let mut random_base = Vec::with_capacity(num_scalar_bits);
        for _ in 0..num_scalar_bits {
            random_base.push(base.clone());
            base = base.double();
        }

        Self { base_window, random_base }
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;
    use snarkvm_curves::ProjectiveCurve;

    const ITERATIONS: u64 = 10;
    const MESSAGE: &str = "PedersenCircuit0";
    const NUM_BITS_MULTIPLIER: u8 = 8;

    fn check_setup<const NUM_BITS: u8>(num_constants: u64, num_public: u64, num_private: u64, num_constraints: u64) {
        for _ in 0..ITERATIONS {
            // Initialize the native Pedersen hash.
            let native = console::Pedersen::<<Circuit as Environment>::Affine, NUM_BITS>::setup(MESSAGE);

            Circuit::scope("Pedersen::setup", || {
                // Perform the setup operation.
                let circuit = Pedersen::<Circuit, NUM_BITS>::setup(MESSAGE);
                assert_scope!(num_constants, num_public, num_private, num_constraints);

                // Check for equivalency of the bases.
                native.base_window().iter().zip_eq(circuit.base_window.iter()).for_each(|(expected, candidate)| {
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
        check_setup::<NUM_BITS_MULTIPLIER>(785, 0, 0, 0);
        check_setup::<{ 2 * NUM_BITS_MULTIPLIER }>(809, 0, 0, 0);
        check_setup::<{ 3 * NUM_BITS_MULTIPLIER }>(833, 0, 0, 0);
        check_setup::<{ 4 * NUM_BITS_MULTIPLIER }>(857, 0, 0, 0);
        check_setup::<{ 5 * NUM_BITS_MULTIPLIER }>(881, 0, 0, 0);
    }
}
