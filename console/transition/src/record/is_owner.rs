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
    /// Returns `true` if this record belongs to the account of the given view key.
    pub fn is_owner(&self, view_key: &ViewKey<N>) -> bool {
        // Compute the record view key := G^r^view_key.
        let record_view_key = self.to_record_view_key(view_key);
        // Compute the candidate MAC := Hash(G^r^view_key).
        match N::hash_psd2(&[N::mac_domain(), record_view_key]) {
            // Check if the MACs match.
            Ok(candidate_mac) => self.mac == candidate_mac,
            // If the computation fails, return false.
            Err(error) => {
                eprintln!("{error}");
                false
            }
        }
    }
}
