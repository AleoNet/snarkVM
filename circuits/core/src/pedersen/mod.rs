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

use snarkvm_circuits_environment::prelude::*;
use snarkvm_circuits_types::{Field, StringType};

pub struct Pedersen<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> {
    pub bases: Vec<Vec<Field<E>>>,
}

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> Pedersen<E, NUM_WINDOWS, WINDOW_SIZE> {
    fn setup(message: StringType<E>) -> Self {
        let bases = (0..NUM_WINDOWS)
            .map(|index| {
                // Construct an indexed message to attempt to sample a base.
                // TODO: investigate if this is safe, or do we need to use hash_to_curve?
                let mut base = Field::<E>::from_bits_le(
                    &StringType::<E>::new(Mode::Public, &format!("{message} at {index}")).to_bits_le(),
                );
                let mut powers = Vec::with_capacity(WINDOW_SIZE);
                for _ in 0..WINDOW_SIZE {
                    powers.push(base.clone());
                    base = base.double();
                }
                powers
            })
            .collect();

        Self { bases }
    }

    fn parameters(&self) -> Vec<Vec<Field<E>>> {
        self.bases.clone()
    }
}
