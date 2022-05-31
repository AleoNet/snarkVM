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
    /// Initializes a new record by encrypting the given state with a given randomizer.
    pub fn encrypt(state: &State<A>, record_view_key: &Field<A>) -> Self {
        // Ensure the balance is less than or equal to 2^52.
        A::assert(state.balance().to_bits_le()[52..].iter().fold(Boolean::constant(false), |acc, bit| acc | bit));

        // Compute the randomizers.
        let randomizers = A::hash_many_psd2(&[A::encryption_domain(), record_view_key.clone()], 2);
        // Encrypt the owner.
        let owner = state.owner().to_field() + &randomizers[0];
        // Encrypt the balance.
        let balance = state.balance().to_field() + &randomizers[1];

        // Compute the MAC := Hash(G^r^view_key).
        let mac = A::hash_psd2(&[A::mac_domain(), record_view_key.clone()]);

        // Compute the randomizer for the balance commitment (i.e. HashToScalar(G^r^view_key));
        let r_bcm = A::hash_to_scalar_psd2(&[A::bcm_domain(), record_view_key.clone()]);
        // Compute the balance commitment := G^balance H^HashToScalar(G^r^view_key).
        let bcm = A::commit_ped64(&state.balance().to_bits_le(), &r_bcm);

        Self {
            program: state.program().clone(),
            process: state.process().clone(),
            owner,
            balance,
            data: state.data().clone(),
            nonce: state.nonce().clone(),
            mac,
            bcm,
        }
    }
}
