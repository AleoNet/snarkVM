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

use crate::algorithms::Pedersen;
use snarkvm_circuits_types::Environment;

pub struct PedersenCompressed<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> {
    crh: Pedersen<E, NUM_WINDOWS, WINDOW_SIZE>,
}

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    PedersenCompressed<E, NUM_WINDOWS, WINDOW_SIZE>
{
    pub fn setup(message: &str) -> Self {
        Self { crh: Pedersen::setup(message) }
    }

    pub fn parameters(&self) -> &Pedersen<E, NUM_WINDOWS, WINDOW_SIZE> {
        &self.crh
    }
}
