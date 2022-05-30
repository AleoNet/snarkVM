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

impl<N: Network> Record<N> {
    /// Returns the record ID.
    pub fn to_id(&self, program: &N::Field, process: &N::Field) -> Result<N::Field> {
        // Retrieve the x-coordinate of the nonce.
        let nonce = self.nonce.to_x_coordinate();
        // Compute the BHP hash of the program state.
        N::hash_bhp1024(
            &[*program, *process, self.owner, self.balance, self.data.to_id()?, nonce, self.mac, self.bcm].to_bits_le(),
        )
    }
}
