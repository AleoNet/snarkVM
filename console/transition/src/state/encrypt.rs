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

impl<N: Network> State<N> {
    /// Returns a new record by encrypting this state using the given randomizer,
    /// which is derived from the view key of the **sender**,
    /// along with the serial numbers and output index in the transition.
    pub fn encrypt(&self, randomizer: &Scalar<N>) -> Result<Record<N>> {
        // Ensure the nonce corresponds to the given randomizer: `nonce == randomizer * G`.
        ensure!(self.nonce == N::g_scalar_multiply(randomizer), "Attempted to encrypt using an invalid randomizer");
        // Compute the record view key as `randomizer * address`.
        let record_view_key = (*self.owner * *randomizer).to_x_coordinate();
        // Encrypt the record and output the state.
        Record::encrypt(self, &record_view_key)
    }
}
