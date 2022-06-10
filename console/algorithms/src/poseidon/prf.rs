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

impl<E: Environment, const RATE: usize> PRF for Poseidon<E, RATE> {
    type Input = Field<E>;
    type Output = Field<E>;
    type Seed = Field<E>;

    #[inline]
    fn prf(&self, seed: &Self::Seed, input: &[Self::Input]) -> Result<Self::Output> {
        // Construct the preimage: seed || input.
        let mut preimage = Vec::with_capacity(1 + input.len());
        preimage.push(*seed);
        preimage.extend_from_slice(input);

        // Hash the preimage to derive the PRF output.
        self.hash(&preimage)
    }
}
