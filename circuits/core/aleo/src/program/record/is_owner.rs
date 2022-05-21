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

impl<A: Aleo> Record<A> {
    /// Returns `true` if this record belongs to the account of the given view key.
    pub fn is_owner(&self, view_key: &ViewKey<A>) -> Boolean<A> {
        // Recover the nonce as a group.
        let nonce = Group::from_x_coordinate(self.nonce.clone());
        // Compute the record view key := G^r^view_key.
        let record_view_key = (nonce * &**view_key).to_x_coordinate();
        // Compute the candidate MAC := Hash(G^r^view_key).
        let candidate_mac = A::hash_psd2(&[A::mac_domain(), record_view_key]);
        // Check if the MACs match.
        self.mac.is_equal(&candidate_mac)
    }
}
