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
    /// Initializes a new record by encrypting the given state with a given randomizer.
    pub fn encrypt(state: &State<N>, randomizer: &N::Scalar) -> Result<Self> {
        // Ensure the nonce matches the given randomizer.
        if state.nonce().to_projective() != N::g_scalar_multiply(randomizer) {
            bail!("Invalid randomizer given to encrypt state into a record")
        }
        // Compute the record view key.
        let record_view_key = (**state.owner() * *randomizer).to_affine().to_x_coordinate();
        // Encrypt the record and output the state.
        Self::encrypt_symmetric(state, &record_view_key)
    }

    /// Initializes a new record by encrypting the given state with a given randomizer.
    pub fn encrypt_symmetric(state: &State<N>, record_view_key: &N::Field) -> Result<Self> {
        // Ensure the balance is less than or equal to 2^52.
        if state.balance().to_bits_le()[52..].iter().all(|bit| !bit) {
            bail!("Failed to encrypt an invalid balance into a record")
        }
        // Compute the randomizers.
        let randomizers = N::hash_many_psd2(&[N::encryption_domain(), *record_view_key], 3);
        // Encrypt the owner.
        let owner = state.owner().to_x_coordinate() + randomizers[0];
        // Encrypt the balance.
        let balance = N::Field::from(*state.balance() as u128) + randomizers[1];

        // Encrypt the data.
        let data = state.data().encrypt_symmetric(&(*record_view_key * randomizers[2]))?;

        // Compute the MAC := Hash(G^r^view_key).
        let mac = N::hash_psd2(&[N::mac_domain(), *record_view_key])?;

        // Compute the randomizer for the balance commitment (i.e. HashToScalar(G^r^view_key));
        let r_bcm = N::hash_to_scalar_psd2(&[N::randomizer_domain(), *record_view_key])?;
        // Compute the balance commitment := G^balance H^HashToScalar(G^r^view_key).
        let bcm = N::commit_ped64(&state.balance().to_bits_le(), &r_bcm)?;

        Ok(Self { owner, balance, data, nonce: *state.nonce(), mac, bcm })
    }
}
