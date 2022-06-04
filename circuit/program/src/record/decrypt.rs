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
    /// Returns the state corresponding to the record using the given view key.
    pub fn decrypt(&self, view_key: &ViewKey<A>) -> State<A> {
        // Compute the record view key := G^r^view_key.
        let record_view_key = (&self.nonce * &**view_key).to_x_coordinate();
        // Decrypt the record.
        let state = self.decrypt_symmetric(&record_view_key);
        // Ensure the owner matches the account of the given view key.
        A::assert_eq(state.owner(), view_key.to_address());
        // Output the state.
        state
    }

    /// Returns the state corresponding to the record using the given record view key.
    pub fn decrypt_symmetric(&self, record_view_key: &Field<A>) -> State<A> {
        // Compute the randomizers.
        let randomizers = A::hash_many_psd2(&[A::encryption_domain(), record_view_key.clone()], 2);
        // Decrypt and recover the owner.
        let owner = Address::from_field(&self.owner - &randomizers[0]);
        // Decrypt and recover the balance.
        let balance = U64::from_field(&self.balance - &randomizers[1]);
        // Ensure the balance is less than or equal to 2^52.
        A::assert(!balance.to_bits_le()[52..].iter().fold(Boolean::constant(false), |acc, bit| acc | bit));

        // Compute the candidate MAC := Hash(G^r^view_key).
        let candidate_mac = A::hash_psd2(&[A::mac_domain(), record_view_key.clone()]);
        // Ensure the MAC matches.
        A::assert_eq(&self.mac, &candidate_mac);

        // Compute the randomizer for the balance commitment (i.e. HashToScalar(G^r^view_key));
        let r_bcm = A::hash_to_scalar_psd2(&[A::bcm_domain(), record_view_key.clone()]);
        // Compute the balance commitment := G^balance H^HashToScalar(G^r^view_key).
        let candidate_bcm = A::commit_ped64(&balance.to_bits_le(), &r_bcm);
        // Ensure the balance commitment matches.
        A::assert_eq(&self.bcm, &candidate_bcm);

        // Output the state.
        State::from((owner, balance, self.data.clone(), self.nonce.clone()))
    }
}
