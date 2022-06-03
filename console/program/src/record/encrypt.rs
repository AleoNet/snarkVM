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
    /// Initializes a new record by encrypting the given state with a given record view key.
    pub fn encrypt(state: &State<N>, record_view_key: &N::Field) -> Result<Self> {
        // Ensure the balance is less than or equal to 2^52.
        ensure!(state.balance().to_bits_le()[52..].iter().all(|bit| !bit), "Attempted to encrypt an invalid balance");
        // Compute the randomizers.
        let randomizers = N::hash_many_psd2(&[N::encryption_domain(), *record_view_key], 3);
        // Encrypt the owner.
        let owner = state.owner().to_x_coordinate() + randomizers[0];
        // Encrypt the balance.
        let balance = N::Field::from(state.balance() as u128) + randomizers[1];

        // // Encrypt the data.
        // let data = state.data().encrypt_symmetric(&(*record_view_key * randomizers[2]))?;

        // Compute the MAC := Hash(G^r^view_key).
        let mac = N::hash_psd2(&[N::mac_domain(), *record_view_key])?;

        // Compute the randomizer for the balance commitment (i.e. HashToScalar(G^r^view_key));
        let r_bcm = N::hash_to_scalar_psd2(&[N::bcm_domain(), *record_view_key])?;
        // Compute the balance commitment := G^balance H^HashToScalar(G^r^view_key).
        let bcm = N::commit_ped64(&state.balance().to_bits_le(), &r_bcm)?;

        Ok(Self {
            program: state.program(),
            process: state.process(),
            owner,
            balance,
            data: state.data(),
            nonce: state.nonce(),
            mac,
            bcm,
        })
    }
}
