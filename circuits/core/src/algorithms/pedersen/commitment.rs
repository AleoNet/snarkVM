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

use snarkvm_algorithms::crypto_hash::hash_to_curve;
use snarkvm_circuits_types::prelude::*;

use std::borrow::Cow;

pub struct PedersenCommitment<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> {
    pedersen_gadget: Pedersen<E, NUM_WINDOWS, WINDOW_SIZE>,
    random_base: Vec<Group<E>>,
}

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    PedersenCommitment<E, NUM_WINDOWS, WINDOW_SIZE>
{
    fn setup(message: &str) -> Self {
        let pedersen_gadget = Pedersen::setup(message);

        // Compute the random base
        let (generator, _, _) = hash_to_curve(&format!("{message} for random base"));
        let mut base = Group::constant(generator);

        let num_scalar_bits = E::ScalarField::size_in_bits();
        let mut random_base = Vec::with_capacity(num_scalar_bits);
        for _ in 0..num_scalar_bits {
            random_base.push(base.clone());
            base = base.double();
        }

        Self { pedersen_gadget, random_base }
    }

    fn commit(&self, input: &[Boolean<E>], randomness: &[Boolean<E>]) -> Group<E> {
        let hash = self.pedersen_gadget.hash_uncompressed(input);

        // Compute h^r
        randomness
            .iter()
            .zip_eq(&self.random_base)
            .map(|(bit, power)| Group::ternary(bit, &power, &Group::zero()))
            .fold(Group::<E>::zero(), |acc, x| acc + x)
    }
}
