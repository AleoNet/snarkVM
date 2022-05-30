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
    /// Returns the program state commitment, given the data ID.
    pub fn to_commitment(&self) -> Result<N::Field> {
        // Compute the BHP hash of the program state.
        N::hash_bhp1024(
            &[
                self.program,
                self.process,
                self.owner.to_x_coordinate(),
                N::Field::from(self.balance as u128),
                self.data.to_id()?,
                self.nonce.to_x_coordinate(),
            ]
            .to_bits_le(),
        )
    }
}
