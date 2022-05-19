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
use snarkvm_circuits_environment::assert_scope;

use crate::algorithms::{Commit, CommitUncompressed, Hash, HashUncompressed};
use snarkvm_circuits_types::prelude::*;
use snarkvm_console_algorithms::Blake2Xs;
use snarkvm_curves::{MontgomeryParameters, TwistedEdwardsParameters};
use snarkvm_utilities::BigInteger;

pub const BHP_CHUNK_SIZE: usize = 3;
pub const BHP_LOOKUP_SIZE: usize = 4;

/// The x-coordinate and y-coordinate of each base on the Montgomery curve.
type BaseLookups<E> = (Vec<Field<E>>, Vec<Field<E>>);

/// BHP256 is a collision-resistant hash function that takes a 256-bit input.
pub type BHP256<E> = BHP<E, 2, 43>;
/// BHP512 is a collision-resistant hash function that takes a 512-bit input.
pub type BHP512<E> = BHP<E, 3, 57>;
/// BHP768 is a collision-resistant hash function that takes a 768-bit input.
pub type BHP768<E> = BHP<E, 6, 43>;
/// BHP1024 is a collision-resistant hash function that takes a 1024-bit input.
pub type BHP1024<E> = BHP<E, 6, 57>;

/// BHP is a collision-resistant hash function that takes a variable-length input.
/// The BHP hash function does *not* behave like a random oracle, see Poseidon for one.
pub struct BHP<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> {
    /// The bases for the BHP hash.
    bases: Vec<Vec<BaseLookups<E>>>,
    /// The random base for the BHP commitment.
    random_base: Vec<Group<E>>,
}

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> BHP<E, NUM_WINDOWS, WINDOW_SIZE> {
    /// Initializes a new instance of BHP with the given setup message.
    pub fn setup(message: &str) -> Self {
        // Calculate the maximum window size.
        let mut maximum_window_size = 0;
        let mut range = <E::ScalarField as PrimeField>::BigInteger::from(2_u64);
        while range < E::ScalarField::modulus_minus_one_div_two() {
            // range < (p-1)/2
            range.muln(4); // range * 2^4
            maximum_window_size += 1;
        }
        assert!(WINDOW_SIZE <= maximum_window_size, "The maximum BHP window size is {maximum_window_size}");

        // Compute the bases.
        let bases = (0..NUM_WINDOWS)
            .map(|index| {
                // Construct an indexed message to attempt to sample a base.
                let (generator, _, _) = Blake2Xs::hash_to_curve(&format!("Aleo.BHP.Base.{message}.{index}"));
                // Inject the new base.
                let mut base = Group::constant(generator);
                // Construct the window with the base.
                let mut powers = Vec::with_capacity(WINDOW_SIZE);
                for _ in 0..WINDOW_SIZE {
                    let mut x_bases = Vec::with_capacity(BHP_LOOKUP_SIZE);
                    let mut y_bases = Vec::with_capacity(BHP_LOOKUP_SIZE);
                    let mut accumulator = base.clone();
                    for _ in 0..BHP_LOOKUP_SIZE {
                        // Convert each base from twisted Edwards point into a Montgomery point.
                        let x = (Field::one() + accumulator.to_y_coordinate())
                            / (Field::one() - accumulator.to_y_coordinate());
                        let y = &x / accumulator.to_x_coordinate();

                        x_bases.push(x);
                        y_bases.push(y);
                        accumulator += &base;
                    }
                    for _ in 0..BHP_LOOKUP_SIZE {
                        base = base.double();
                    }
                    powers.push((x_bases, y_bases));
                }
                powers
            })
            .collect::<Vec<Vec<BaseLookups<E>>>>();
        debug_assert_eq!(bases.len(), NUM_WINDOWS, "Incorrect number of windows ({}) for BHP", bases.len());
        bases.iter().for_each(|window| debug_assert_eq!(window.len(), WINDOW_SIZE));

        // Compute the random base.
        let random_base = {
            let (generator, _, _) = Blake2Xs::hash_to_curve(&format!("Aleo.BHP.RandomBase.{message}"));
            let mut base = Group::constant(generator);

            let num_scalar_bits = E::ScalarField::size_in_bits();
            let mut random_base = Vec::with_capacity(num_scalar_bits);
            for _ in 0..num_scalar_bits {
                random_base.push(base.clone());
                base = base.double();
            }
            random_base
        };

        Self { bases, random_base }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_circuits_types::Eject;
    use snarkvm_console::algorithms::BHP as NativeBHP;
    use snarkvm_curves::{AffineCurve, ProjectiveCurve};

    const ITERATIONS: usize = 10;
    const MESSAGE: &str = "BHPCircuit0";

    #[test]
    fn test_setup_constant() {
        for _ in 0..ITERATIONS {
            let native = NativeBHP::<<Circuit as Environment>::Affine, 8, 32>::setup(MESSAGE);
            let circuit = BHP::<Circuit, 8, 32>::setup(MESSAGE);

            native.bases().iter().zip(circuit.bases.iter()).for_each(|(native_bases, circuit_bases)| {
                native_bases.iter().zip(circuit_bases).for_each(|(native_base, circuit_base_lookups)| {
                    // Check the first circuit base (when converted back to twisted Edwards) matches the native one.
                    let (circuit_x, circuit_y) = {
                        let (x_bases, y_bases) = circuit_base_lookups;
                        // Convert the Montgomery point to a twisted Edwards point.
                        let edwards_x = &x_bases[0] / &y_bases[0]; // 1 constraint
                        let edwards_y = (&x_bases[0] - Field::one()) / (&x_bases[0] + Field::one());
                        (edwards_x, edwards_y)
                    };
                    assert_eq!(native_base.to_affine().to_x_coordinate(), circuit_x.eject_value());
                    assert_eq!(native_base.to_affine().to_y_coordinate(), circuit_y.eject_value());
                })
            });
        }
    }
}
