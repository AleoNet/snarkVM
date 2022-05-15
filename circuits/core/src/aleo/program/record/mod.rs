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

// #[cfg(test)]
// use snarkvm_circuits_types::environment::assert_scope;

use crate::aleo::{Aleo, State, ViewKey};
use snarkvm_circuits_types::{environment::prelude::*, Address, Boolean, Field, Group, Scalar, U64};

// TODO (howardwu): Check mode is only public/private, not constant.
/// A program's record is a set of **ciphertext** variables used by a program.
/// Note: `Record` is the **encrypted** form of `State`.
pub struct Record<A: Aleo> {
    /// The program this record belongs to.
    program: Field<A>,
    /// The **encrypted** address this record belongs to (i.e. `owner + HashMany(G^r^view_key, 2)[0]`).
    owner: Field<A>,
    /// The **encrypted** balance in this record (i.e. `balance.to_field() + HashMany(G^r^view_key, 2)[1]`).
    balance: Field<A>,
    /// The ID for the program data.
    data: Field<A>,
    /// The nonce for this record (i.e. `G^r`).
    nonce: Field<A>,
    /// The MAC for this record (i.e. `Hash(G^r^view_key)`).
    mac: Field<A>,
    /// The balance commitment for this record (i.e. `G^balance H^HashToScalar(G^r^view_key)`).
    bcm: Field<A>,
}

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

    /// Initializes a new record by encrypting the given state with a given randomizer.
    pub fn encrypt(state: &State<A>, randomizer: &Scalar<A>) -> Self {
        // Ensure the nonce matches the given randomizer.
        A::assert_eq(state.nonce(), A::g_scalar_multiply(randomizer).to_x_coordinate());

        // Compute the record view key.
        let record_view_key = (state.owner().to_group() * randomizer).to_x_coordinate();
        // Encrypt the record.
        let state = Self::encrypt_symmetric(state, &record_view_key);
        // Output the state.
        state
    }

    /// Initializes a new record by encrypting the given state with a given randomizer.
    pub fn encrypt_symmetric(state: &State<A>, record_view_key: &Field<A>) -> Self {
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
        let r_bcm = A::hash_to_scalar_psd2(&[A::randomizer_domain(), record_view_key.clone()]);
        // Compute the balance commitment := G^balance H^HashToScalar(G^r^view_key).
        let bcm = A::commit_ped64(&state.balance().to_bits_le(), &r_bcm);

        Self {
            program: state.program().clone(),
            owner,
            balance,
            data: state.data().clone(),
            nonce: state.nonce().clone(),
            mac,
            bcm,
        }
    }

    /// Returns the state corresponding to the record using the given view key.
    pub fn decrypt(&self, view_key: &ViewKey<A>) -> State<A> {
        // Recover the nonce as a group.
        let nonce = Group::from_x_coordinate(self.nonce.clone());
        // Compute the record view key := G^r^view_key.
        let record_view_key = (nonce * &**view_key).to_x_coordinate();

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
        A::assert(balance.to_bits_le()[52..].iter().fold(Boolean::constant(false), |acc, bit| acc | bit));

        // Compute the candidate MAC := Hash(G^r^view_key).
        let candidate_mac = A::hash_psd2(&[A::mac_domain(), record_view_key.clone()]);
        // Ensure the MAC matches.
        A::assert_eq(&self.mac, &candidate_mac);

        // Compute the randomizer for the balance commitment (i.e. HashToScalar(G^r^view_key));
        let r_bcm = A::hash_to_scalar_psd2(&[A::randomizer_domain(), record_view_key.clone()]);
        // Compute the balance commitment := G^balance H^HashToScalar(G^r^view_key).
        let candidate_bcm = A::commit_ped64(&balance.to_bits_le(), &r_bcm);
        // Ensure the balance commitment matches.
        A::assert_eq(&self.bcm, &candidate_bcm);

        // Output the state.
        State::from((self.program.clone(), owner, balance, self.data.clone(), self.nonce.clone()))
    }
}

impl<A: Aleo> TypeName for Record<A> {
    fn type_name() -> &'static str {
        "record"
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
