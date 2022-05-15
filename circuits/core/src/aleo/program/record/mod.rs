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

mod to_commitment;

use crate::aleo::{Aleo, State};
use snarkvm_circuits_types::{environment::prelude::*, Address, Boolean, Field, Scalar, U64};

pub(super) const NUM_DATA_FIELD_ELEMENTS: usize = 4;

// TODO (howardwu): Check mode is only public/private, not constant.
/// A program's record is a set of **ciphertext** variables used by a program.
/// Note: `Record` is the **encrypted** form of `State`.
pub struct Record<A: Aleo> {
    /// The program this record belongs to.
    program: Field<A>,
    /// The **encrypted** address this record belongs to
    /// (i.e. `state.owner.to_x_coordinate() + HashMany(G^r^view_key)[0]`).
    owner: Field<A>,
    /// The **encrypted** balance in this record
    /// (i.e. `state.balance.to_field() + HashMany(G^r^view_key)[1]`).
    balance: Field<A>,
    /// The **encrypted** data in this record
    /// (i.e. `state.data.to_fields() (+) HashMany(G^r^view_key)[2..]`).
    data: [Field<A>; NUM_DATA_FIELD_ELEMENTS],
    /// The nonce for this record (i.e. `G^r`).
    nonce: Field<A>,
    /// The MAC for this record (i.e. `Hash(G^r^view_key)`).
    mac: Field<A>,
    /// The balance commitment for this record (i.e. `G^state.balance H^r`).
    bcm: Field<A>,
}

impl<A: Aleo> Record<A> {
    /// Creates a new record from the given state.
    pub fn from_state(state: State<A>, randomizer: Scalar<A>) -> Self {
        // The number of ciphertext randomizers is set to encrypt the owner, balance, and data.
        const NUM_RANDOMIZERS: usize = 2 + NUM_DATA_FIELD_ELEMENTS;

        // Ensure the randomizer corresponds to the nonce.
        A::assert_eq(state.nonce(), A::g_scalar_multiply(&randomizer).to_x_coordinate());

        // Encrypt the owner, balance, and data.
        let (record_view_key, owner, balance, data) = {
            // Construct the plaintext.
            let mut plaintext = Vec::with_capacity(NUM_RANDOMIZERS);
            plaintext.push(state.owner().to_group().to_x_coordinate());
            plaintext.push(state.balance().to_field());
            plaintext.extend_from_slice(&Self::encode_message(&state.data().to_bits_le()));

            // Ensure the number of plaintext elements is within the number of allowed randomizers.
            if plaintext.len() > NUM_RANDOMIZERS {
                A::halt(format!("Attempted to encrypt {} elements, maximum is {NUM_RANDOMIZERS}", plaintext.len()))
            } else {
                // Pad up to the number of randomizers, if there are less plaintext elements.
                plaintext.resize(NUM_RANDOMIZERS, Field::zero());
            }

            // Compute the record view key.
            let record_view_key = (state.owner().to_group() * &randomizer).to_x_coordinate();
            // Compute the randomizers.
            let randomizers = A::hash_many_psd2(
                &[
                    Field::constant(A::BaseField::from_bytes_le_mod_order(b"AleoSymmetricEncryption0")),
                    record_view_key.clone(),
                ],
                NUM_RANDOMIZERS,
            );

            // Compute the ciphertext.
            let ciphertext = plaintext.iter().zip_eq(randomizers).map(|(p, r)| p + r).collect::<Vec<_>>();

            // Prepare the response.
            let owner = ciphertext[0].clone();
            let balance = ciphertext[1].clone();
            let data: [Field<A>; NUM_DATA_FIELD_ELEMENTS] =
                [ciphertext[2].clone(), ciphertext[3].clone(), ciphertext[4].clone(), ciphertext[5].clone()];

            (record_view_key, owner, balance, data)
        };

        // Compute the MAC := Hash(G^r^view_key).
        let mac = A::hash_psd2(&[
            Field::constant(A::BaseField::from_bytes_le_mod_order(b"AleoSymmetricKeyCommitment0")),
            record_view_key,
        ]);

        // Compute the balance commitment := G^state.balance H^r.
        let bcm = A::commit_ped64(&state.balance().to_bits_le(), &randomizer);

        Self { program: state.program().clone(), owner, balance, data, nonce: state.nonce().clone(), mac, bcm }
    }

    /// Encode a bitstring into a vector of field elements. This is used to convert messages
    /// to hashable [`Field`] elements.
    fn encode_message(message: &[Boolean<A>]) -> Vec<Field<A>> {
        // Add an extra bit to the message.
        // The final bit serves as a terminus indicator,
        // and is used during decryption to ensure the length is correct.
        let mut bits = message.to_vec();
        bits.push(Boolean::constant(true));

        // Pack the bits into field elements.
        bits.chunks(A::BaseField::size_in_data_bits()).map(Field::from_bits_le).collect()
    }

    //     /// Returns the record owner.
    //     pub fn owner(&self) -> &Address<A> {
    //         &self.owner
    //     }
    //
    //     /// Returns the record balance.
    //     pub fn balance(&self) -> &U64<A> {
    //         &self.balance
    //     }
    //
    //     /// Returns the record data.
    //     pub fn data(&self) -> &Vec<Literal<A>> {
    //         &self.data
    //     }
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
