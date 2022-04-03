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

use snarkvm_algorithms::crypto_hash::hash_to_curve;
use snarkvm_circuits_types::prelude::*;

pub struct Pedersen<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> {
    /// The base windows for the Pedersen hash.
    bases: Vec<Vec<Group<E>>>,
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
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_algorithms::{crh::PedersenCRH, CRH};
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_curves::{AffineCurve, ProjectiveCurve};

    const ITERATIONS: usize = 10;
    const MESSAGE: &str = "PedersenCircuit0";
    const WINDOW_SIZE_MULTIPLIER: usize = 8;

    type Projective = <<Circuit as Environment>::Affine as AffineCurve>::Projective;

    fn check_setup<const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>() {
        for _ in 0..ITERATIONS {
            let native = PedersenCRH::<Projective, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);
            let circuit = Pedersen::<Circuit, NUM_WINDOWS, WINDOW_SIZE>::setup(MESSAGE);

            // Check for equivalency of the bases.
            native.parameters().iter().flatten().zip(circuit.bases.iter().flatten()).for_each(
                |(expected, candidate)| {
                    assert_eq!(expected.to_affine(), candidate.eject_value());
                },
            );
        }
    }

    #[test]
    fn test_setup_constant() {
        check_setup::<1, WINDOW_SIZE_MULTIPLIER>();
        check_setup::<2, { 2 * WINDOW_SIZE_MULTIPLIER }>();
        check_setup::<3, { 3 * WINDOW_SIZE_MULTIPLIER }>();
        check_setup::<4, { 4 * WINDOW_SIZE_MULTIPLIER }>();
        check_setup::<5, { 5 * WINDOW_SIZE_MULTIPLIER }>();
        check_setup::<6, { 6 * WINDOW_SIZE_MULTIPLIER }>();
        check_setup::<7, { 7 * WINDOW_SIZE_MULTIPLIER }>();
        check_setup::<8, { 8 * WINDOW_SIZE_MULTIPLIER }>();
        check_setup::<9, { 9 * WINDOW_SIZE_MULTIPLIER }>();
        check_setup::<10, { 10 * WINDOW_SIZE_MULTIPLIER }>();
    }
}
