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
    /// Returns the state corresponding to the record using the given view key.
    pub fn decrypt(&self, view_key: &ViewKey<N>) -> Result<State<N>> {
        // Compute the record view key := G^r^view_key.
        let record_view_key = (self.nonce * **view_key).to_x_coordinate();
        // Decrypt the record.
        let state = self.decrypt_symmetric(&record_view_key)?;
        // Ensure the owner matches the account of the given view key.
        ensure!(state.owner() == Address::try_from(view_key)?, "Failed to decrypt a record with the given view key");
        // Output the state.
        Ok(state)
    }

    /// Returns the state corresponding to the record using the given record view key.
    pub fn decrypt_symmetric(&self, record_view_key: &Field<N>) -> Result<State<N>> {
        // Compute the candidate MAC := Hash(G^r^view_key).
        let candidate_mac = N::hash_psd2(&[N::mac_domain(), *record_view_key])?;
        // Ensure the MAC matches.
        ensure!(self.mac == candidate_mac, "Failed to decrypt using the given record view key");

        // Compute the randomizers.
        let randomizers = N::hash_many_psd2(&[N::encryption_domain(), *record_view_key], 3);

        // Decrypt and recover the owner.
        let owner = Address::new(Group::from_x_coordinate(self.owner - randomizers[0])?);

        // Decrypt the balance.
        let balance = (self.balance - randomizers[1]).to_bytes_le()?;
        // Ensure the balance is less than or equal to 2^52.
        ensure!(balance.to_bits_le()[52..].iter().all(|bit| !bit), "Attempted to decrypt an invalid balance to state");
        // Recover the balance.
        let balance = u64::from_le_bytes(balance[0..8].try_into()?);

        // // Decrypt the data.
        // let data = self.data.decrypt_symmetric(&(*record_view_key * randomizers[2]))?;

        // Compute the randomizer for the balance commitment (i.e. HashToScalar(G^r^view_key));
        let r_bcm = N::hash_to_scalar_psd2(&[N::bcm_domain(), *record_view_key])?;
        // Compute the balance commitment := G^balance H^HashToScalar(G^r^view_key).
        let candidate_bcm = N::commit_ped64(&balance.to_bits_le(), &r_bcm)?;
        // Ensure the balance commitment matches.
        ensure!(self.bcm == candidate_bcm, "Failed to decrypt the balance commitment");

        // Output the state.
        Ok(State::new(owner, balance, self.data, self.nonce))
    }
}
