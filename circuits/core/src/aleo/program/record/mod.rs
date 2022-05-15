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
use snarkvm_circuits_types::{environment::prelude::*, Boolean, Field, Group, Scalar};

pub(super) const NUM_DATA_FIELD_ELEMENTS: usize = 4;

// TODO (howardwu): Check mode is only public/private, not constant.
/// A program's record is a set of **ciphertext** variables used by a program.
/// Note: `Record` is the **encrypted** form of `State`.
pub struct Record<A: Aleo> {
    /// The program this record belongs to.
    program: Field<A>,
    /// The **encrypted** address this record belongs to (i.e. `owner + HashMany(G^r^view_key)[0]`).
    owner: Field<A>,
    /// The **encrypted** balance in this record (i.e. `balance.to_field() + HashMany(G^r^view_key)[1]`).
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

// /// The balance commitment for this record (i.e. `G^state.balance H^r`).
//
// // Compute the balance commitment := G^state.balance H^r.
// let bcm = A::commit_ped64(&state.balance().to_bits_le(), &randomizer);

impl<A: Aleo> Record<A> {
    /// Returns `true` if this record belongs to the account of the given view key.
    pub fn is_owner(&self, view_key: &ViewKey<A>) -> Boolean<A> {
        // Recover the nonce as a group.
        let nonce = Group::from_x_coordinate(self.nonce.clone());
        // Compute the record view key := G^r^view_key.
        let record_view_key = (nonce * &**view_key).to_x_coordinate();
        // Compute the candidate MAC := Hash(G^r^view_key).
        let candidate = A::hash_psd2(&[A::mac_domain(), record_view_key]);
        // Check if the MACs match.
        self.mac.is_equal(&candidate)
    }

    /// Creates a new record from the given state.
    pub fn from_state(state: State<A>, randomizer: Scalar<A>) -> Self {
        // Compute the record view key.
        let record_view_key = (state.owner().to_group() * &randomizer).to_x_coordinate();

        // Encrypt the owner and balance.
        let (owner, balance) = {
            // Construct the plaintext.
            let plaintext = vec![state.owner().to_group().to_x_coordinate(), state.balance().to_field()];
            // Compute the randomizers.
            let randomizers = A::hash_many_psd2(&[A::encryption_domain(), record_view_key.clone()], plaintext.len());
            // Compute the ciphertext.
            let ciphertext = plaintext.iter().zip_eq(randomizers).map(|(p, r)| p + r).collect::<Vec<_>>();
            // Output the encrypted owner and balance.
            (ciphertext[0].clone(), ciphertext[1].clone())
        };

        // Compute the MAC := Hash(G^r^view_key).
        let mac = A::hash_psd2(&[A::mac_domain(), record_view_key.clone()]);

        // Compute the randomizer for the balance commitment (i.e. HashToScalar(G^r^view_key));
        let r_bcm = A::hash_to_scalar_psd2(&[A::randomizer_domain(), record_view_key]);
        // Compute the balance commitment := G^state.balance H^HashToScalar(G^r^view_key).
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
