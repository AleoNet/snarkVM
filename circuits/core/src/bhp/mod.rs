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

#[cfg(test)]
use snarkvm_circuits_environment::assert_scope;

use snarkvm_algorithms::crypto_hash::hash_to_curve;
use snarkvm_circuits_types::prelude::*;
use snarkvm_utilities::BigInteger;

pub const BHP_CHUNK_SIZE: usize = 3;
pub const BHP_LOOKUP_SIZE: usize = 4;

pub struct BHPCRH<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> {
    bases: Vec<Vec<Group<E>>>,
}

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> BHPCRH<E, NUM_WINDOWS, WINDOW_SIZE> {
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
                let (generator, _, _) = hash_to_curve(&format!("{message} at {index}"));
                // Inject the new base.
                let mut base = Group::constant(generator);
                // Construct the window with the base.
                let mut powers = Vec::with_capacity(WINDOW_SIZE);
                for _ in 0..WINDOW_SIZE {
                    powers.push(base.clone());
                    for _ in 0..BHP_LOOKUP_SIZE {
                        base = base.double();
                    }
                }
                powers
            })
            .collect::<Vec<Vec<Group<E>>>>();
        debug_assert_eq!(bases.len(), NUM_WINDOWS, "Incorrect number of windows ({}) for BHP", bases.len());
        bases.iter().for_each(|window| debug_assert_eq!(window.len(), WINDOW_SIZE));

        Self { bases }
    }

    pub fn parameters(&self) -> &Vec<Vec<Group<E>>> {
        &self.bases
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_algorithms::{crh::BHPCRH as NativeBHP, CRH};
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_circuits_types::Eject;
    use snarkvm_curves::{edwards_bls12::EdwardsProjective, ProjectiveCurve};

    const ITERATIONS: usize = 10;
    const MESSAGE: &str = "bhp_gadget_setup_test";

    #[test]
    fn test_setup_constant() {
        for _ in 0..ITERATIONS {
            let native_hasher = NativeBHP::<EdwardsProjective, 8, 32>::setup(MESSAGE);
            let circuit_hasher = BHPCRH::<Circuit, 8, 32>::setup(MESSAGE);

            native_hasher.parameters().iter().zip(circuit_hasher.parameters().iter()).for_each(
                |(native_bases, circuit_bases)| {
                    native_bases.iter().zip(circuit_bases).for_each(|(native_base, circuit_base)| {
                        assert_eq!(native_base.to_affine(), circuit_base.eject_value());
                    })
                },
            );
        }
    }
}
