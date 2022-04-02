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

use snarkvm_circuits_types::{Boolean, Environment, Field, Group, Ternary};

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> BHPCRH<E, NUM_WINDOWS, WINDOW_SIZE> {
    pub fn hash(&self, input: &[Boolean<E>]) -> Field<E> {
        self.hash_bits_inner(input).to_x_coordinate()
    }

    fn hash_bits_inner(&self, input: &[Boolean<E>]) -> Group<E> {
        let constant_false = Boolean::<E>::constant(false);

        // Ensure the input size is within the parameter size,
        if input.len() > NUM_WINDOWS * WINDOW_SIZE * BHP_CHUNK_SIZE {
            E::halt("Incorrect input length")
        }

        // Pad the input to a multiple of `BHP_CHUNK_SIZE` for hashing.
        let mut input = input.to_vec();
        if input.len() % BHP_CHUNK_SIZE != 0 {
            let padding = BHP_CHUNK_SIZE - (input.len() % BHP_CHUNK_SIZE);
            input.extend_from_slice(&vec![constant_false; BHP_CHUNK_SIZE][..padding]);
            assert_eq!(input.len() % BHP_CHUNK_SIZE, 0);
        }

        // Compute sum of h_i^{sum of (1-2*c_{i,j,2})*(1+c_{i,j,0}+2*c_{i,j,1})*2^{4*(j-1)} for all j in segment}
        // for all i. Described in section 5.4.1.7 in the Zcash protocol specification.
        //
        // Note: `.zip()` is used here (as opposed to `.zip_eq()`) as the input can be less than
        // `NUM_WINDOWS * WINDOW_SIZE * BHP_CHUNK_SIZE` in length, which is the parameter size here.
        let zero = Group::<E>::zero();
        input
            .chunks(WINDOW_SIZE * BHP_CHUNK_SIZE)
            .flat_map(|bits| {
                bits.chunks(BHP_CHUNK_SIZE).zip(self.bases.iter()).map(|(chunk_bits, base)| {
                    let mut powers = vec![];
                    let mut base_power = base.clone();
                    for _ in 0..4 {
                        powers.push(base_power.clone());
                        base_power = base_power.double();
                    }

                    let mut result = Group::<E>::zero();
                    result += &powers[0];
                    result += Group::ternary(&chunk_bits[0], &(&powers[1] - &powers[0]), &zero);
                    result += Group::ternary(&chunk_bits[1], &(&powers[2] - &powers[0]), &zero);
                    result += Group::ternary(
                        &(&chunk_bits[0] & &chunk_bits[1]),
                        &(&powers[3] - &powers[2] - &powers[1] + &powers[0]),
                        &zero,
                    );
                    result
                })
            })
            .fold(Group::zero(), |acc, x| acc + x)
    }
}
