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

use snarkvm_algorithms::crypto_hash::hash_to_curve;
use snarkvm_circuits_environment::Mode;
use snarkvm_circuits_types::{Double, Environment, Group, Inject, Zero};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::BigInteger;

pub const BHP_CHUNK_SIZE: usize = 3;
pub const BHP_LOOKUP_SIZE: usize = 2usize.pow(BHP_CHUNK_SIZE as u32);

pub struct BHPCRH<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> {
    bases: Vec<Group<E>>,
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
                Group::new(Mode::Constant, generator)
            })
            .collect::<Vec<Group<E>>>();
        debug_assert_eq!(bases.len(), NUM_WINDOWS, "Incorrect number of windows ({:?}) for BHP", bases.len());

        Self { bases }
    }

    pub fn parameters(&self) -> &Vec<Group<E>> {
        &self.bases
    }
}
