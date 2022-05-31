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

impl<A: Aleo> State<A> {
    /// Returns a new record by encrypting this state with the given randomizer.
    pub fn encrypt(&self, randomizer: &Randomizer<A>) -> Record<A> {
        // Ensure the nonce matches the given randomizer.
        A::assert_eq(&self.nonce, randomizer.to_nonce());

        // Compute the record view key.
        let record_view_key = (self.owner.to_group() * randomizer.value()).to_x_coordinate();
        // Encrypt the state and output the record.
        Record::encrypt(self, &record_view_key)
    }
}
