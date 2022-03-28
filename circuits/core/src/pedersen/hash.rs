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

use super::Pedersen;

use snarkvm_circuits_types::{Boolean, Eject, Environment, Group, Inject, Itertools, Zero};

use std::borrow::Cow;

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> Pedersen<E, NUM_WINDOWS, WINDOW_SIZE> {
    fn hash(&self, input: &[Boolean<E>]) -> Group<E> {
        let constant_false = Boolean::<E>::constant(false);

        let mut input = Cow::Borrowed(input);
        match input.len() <= WINDOW_SIZE * NUM_WINDOWS {
            // Pad the input if it is under the required parameter size.
            true => input.to_mut().resize(WINDOW_SIZE * NUM_WINDOWS, constant_false),
            // Ensure the input size is within the parameter size,
            false => E::halt("incorrect input length for pedersen hash"),
        }

        // Compute sum of h_i^{m_i} for all i.
        input
            .chunks(WINDOW_SIZE)
            .zip_eq(&self.bases)
            .flat_map(|(bits, powers)| {
                bits.iter().zip_eq(powers).flat_map(|(bit, base)| match bit.eject_value() {
                    true => Some(base.clone()),
                    false => None,
                })
            })
            .fold(Group::<E>::zero(), |acc, x| acc + x)
    }
}
