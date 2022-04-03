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
use snarkvm_circuits_types::{Boolean, Environment, Field};

impl<E: Environment, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    PedersenCompressed<E, NUM_WINDOWS, WINDOW_SIZE>
{
    /// Returns the affine x-coordinate as the collision-resistant hash output.
    pub fn hash(&self, input: &[Boolean<E>]) -> Field<E> {
        self.crh.hash(input).to_x_coordinate()
    }
}
