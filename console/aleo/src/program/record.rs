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

use crate::{Address, Network, State, ViewKey};
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_utilities::{ToBits, ToBytes};

use anyhow::{bail, Result};

/// A program's record is a set of **ciphertext** variables used by a program.
/// Note: `Record` is the **encrypted** form of `State`.
pub struct Record<N: Network> {
    /// The **encrypted** address this record belongs to (i.e. `owner + HashMany(G^r^view_key, 2)[0]`).
    owner: N::Field,
    /// The **encrypted** balance in this record (i.e. `balance.to_field() + HashMany(G^r^view_key, 2)[1]`).
    balance: N::Field,
    /// The ID for the program data.
    data: N::Field,
    /// The nonce for this record (i.e. `G^r`).
    nonce: N::Affine,
    /// The MAC for this record (i.e. `Hash(G^r^view_key)`).
    mac: N::Field,
    /// The balance commitment for this record (i.e. `G^balance H^HashToScalar(G^r^view_key)`).
    bcm: N::Field,
}

impl<N: Network> Record<N> {
    /// Returns `true` if this record belongs to the account of the given view key.
    pub fn is_owner(&self, view_key: &ViewKey<N>) -> bool {
        // Compute the record view key := G^r^view_key.
        let record_view_key = (self.nonce * **view_key).to_affine().to_x_coordinate();
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

    /// Returns the record ID.
    pub fn to_id(&self, program: &N::Field, process: &N::Field) -> Result<N::Field> {
        // TODO (howardwu): Abstraction - add support for a custom BHP hash size.
        // Compute the BHP hash of the program state.
        let left = N::hash_bhp1024(&[*program, *process, self.owner, self.balance].to_bits_le())?;
        let right = N::hash_bhp1024(&[self.data, self.nonce.to_x_coordinate(), self.mac, self.bcm].to_bits_le())?;
        N::hash_bhp512(&[left, right].to_bits_le())
    }

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
        let randomizers = N::hash_many_psd2(&[N::encryption_domain(), *record_view_key], 2);
        // Encrypt the owner.
        let owner = state.owner().to_x_coordinate() + randomizers[0];
        // Encrypt the balance.
        let balance = N::Field::from(*state.balance() as u128) + randomizers[1];

        // Compute the MAC := Hash(G^r^view_key).
        let mac = N::hash_psd2(&[N::mac_domain(), *record_view_key])?;

        // Compute the randomizer for the balance commitment (i.e. HashToScalar(G^r^view_key));
        let r_bcm = N::hash_to_scalar_psd2(&[N::randomizer_domain(), *record_view_key])?;
        // Compute the balance commitment := G^balance H^HashToScalar(G^r^view_key).
        let bcm = N::commit_ped64(&state.balance().to_bits_le(), &r_bcm)?;

        Ok(Self { owner, balance, data: *state.data(), nonce: *state.nonce(), mac, bcm })
    }

    /// Returns the state corresponding to the record using the given view key.
    pub fn decrypt(&self, view_key: &ViewKey<N>) -> Result<State<N>> {
        // Compute the record view key := G^r^view_key.
        let record_view_key = (self.nonce * **view_key).to_affine().to_x_coordinate();
        // Decrypt the record.
        let state = self.decrypt_symmetric(&record_view_key)?;
        // Ensure the owner matches the account of the given view key.
        match *state.owner() == Address::try_from(view_key)? {
            // Output the state.
            true => Ok(state),
            // Abort the decryption.
            false => bail!("Failed to decrypt a record with the given view key"),
        }
    }

    /// Returns the state corresponding to the record using the given record view key.
    pub fn decrypt_symmetric(&self, record_view_key: &N::Field) -> Result<State<N>> {
        // Compute the candidate MAC := Hash(G^r^view_key).
        let candidate_mac = N::hash_psd2(&[N::mac_domain(), *record_view_key])?;
        // Ensure the MAC matches.
        if self.mac != candidate_mac {
            bail!("Failed to decrypt using the given record view key")
        }

        // Compute the randomizers.
        let randomizers = N::hash_many_psd2(&[N::encryption_domain(), *record_view_key], 2);

        // Decrypt and recover the owner.
        let owner = Address(N::affine_from_x_coordinate(self.owner - randomizers[0])?);

        // Decrypt the balance.
        let balance = (self.balance - randomizers[1]).to_bytes_le()?;
        // Ensure the balance is less than or equal to 2^52.
        if balance.to_bits_le()[52..].iter().all(|bit| !bit) {
            bail!("Failed to decrypt an invalid balance into state")
        }
        // Recover the balance.
        let balance = u64::from_le_bytes(balance[0..8].try_into()?);

        // Compute the randomizer for the balance commitment (i.e. HashToScalar(G^r^view_key));
        let r_bcm = N::hash_to_scalar_psd2(&[N::randomizer_domain(), *record_view_key])?;
        // Compute the balance commitment := G^balance H^HashToScalar(G^r^view_key).
        let candidate_bcm = N::commit_ped64(&balance.to_bits_le(), &r_bcm)?;
        // Ensure the balance commitment matches.
        if self.bcm != candidate_bcm {
            bail!("Failed to decrypt the balance commitment")
        }

        // Output the state.
        Ok(State::from((owner, balance, self.data, self.nonce)))
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::aleo::Devnet as Circuit;
//     use snarkvm_circuits_types::Group;
//
//     #[test]
//     fn test_record() {
//         let first = Literal::<Circuit>::from_str("10field.public");
//         let second = Literal::from_str("true.private");
//         let third = Literal::from_str("99i64.public");
//
//         let _candidate = Record::<Circuit> {
//             owner: Address::from(Group::from_str("2group.private")),
//             value: I64::from_str("1i64.private"),
//             data: vec![first, second, third],
//         };
//     }
// }
