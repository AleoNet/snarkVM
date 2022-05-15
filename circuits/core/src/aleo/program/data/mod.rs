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

use crate::aleo::Aleo;
use snarkvm_circuits_types::{environment::prelude::*, Address, Boolean, Field, Group, Scalar};

pub trait DataType<A: Aleo>: Clone + Eject + ToBits<Boolean = Boolean<A>> + FromBits<Boolean = Boolean<A>> {}

#[derive(Clone)]
pub enum Data<A: Aleo, D: DataType<A>> {
    /// Publicly-visible data.
    Plaintext(D, Mode),
    /// Private data encrypted under the account owner's address.
    Ciphertext(Vec<Field<A>>, Mode),
}

// // TODO (howardwu): Abstraction - Replace data with an ID.
// let data = A::hash_bhp1024(&self.data.to_bits_le());

impl<A: Aleo, D: DataType<A>> Data<A, D> {
    /// Returns the mode of the data.
    pub fn mode(&self) -> Mode {
        match self {
            Self::Plaintext(_, mode) => *mode,
            Self::Ciphertext(_, mode) => *mode,
        }
    }

    /// Returns `true` if the enum variant corresponds to the correct mode.
    /// Otherwise, the method returns `false`.
    pub fn is_valid(&self) -> bool {
        match self {
            Self::Plaintext(_, mode) => mode.is_constant() || mode.is_public(),
            Self::Ciphertext(_, mode) => mode.is_private(),
        }
    }

    /// Encrypts `self` under the given Aleo address and randomizer,
    /// turning `self` into `Data::Ciphertext(..)` if the `mode` is private.
    /// Note: The output is guaranteed to satisfy `Data::is_valid(output)`.
    pub fn encrypt(&self, address: Address<A>, randomizer: Scalar<A>) -> Self {
        match self {
            Self::Plaintext(data, Mode::Private) => {
                // Encode the data as field elements.
                let plaintext = Self::encode(data);
                // Compute the data view key.
                let data_view_key = (address.to_group() * randomizer).to_x_coordinate();
                // Prepare a randomizer for each field element.
                let randomizers = A::hash_many_psd8(&[A::encryption_domain(), data_view_key], plaintext.len());
                // Compute the ciphertext field elements.
                let ciphertext = plaintext.iter().zip_eq(randomizers).map(|(p, r)| p + r).collect();
                // Output the ciphertext.
                Self::Ciphertext(ciphertext, Mode::Private)
            }
            _ => (*self).clone(),
        }
    }

    /// Decrypts `self` into plaintext using the given view key & nonce,
    /// turning `Data::Ciphertext(..)` into `Data::Plaintext(..)`.
    /// Note: The output does **not** necessarily satisfy `Data::is_valid(output)`.
    pub fn decrypt(&self, view_key: Scalar<A>, nonce: Field<A>) -> Self {
        match self {
            Self::Plaintext(..) => (*self).clone(),
            Self::Ciphertext(ciphertext, mode) => {
                // Recover the nonce as a group.
                let nonce = Group::from_x_coordinate(nonce);
                // Compute the data view key.
                let data_view_key = (view_key * nonce).to_x_coordinate();
                // Prepare a randomizer for each field element.
                let randomizers = A::hash_many_psd8(&[A::encryption_domain(), data_view_key], ciphertext.len());
                // Compute the plaintext field elements.
                let plaintext: Vec<_> = ciphertext.iter().zip_eq(randomizers).map(|(c, r)| c - r).collect();
                // Decode the data from field elements, and output the plaintext.
                Self::Plaintext(Self::decode(&plaintext), *mode)
            }
        }
    }
}

impl<A: Aleo, D: DataType<A>> Data<A, D> {
    /// Returns a list of field elements encoding the given data.
    fn encode(data: &D) -> Vec<Field<A>> {
        // Encode the data as little-endian bits.
        let mut bits = data.to_bits_le();
        // Adds one final bit to the data, to serve as a terminus indicator.
        // During decryption, this final bit ensures we've reached the end.
        bits.push(Boolean::constant(true));
        // Pack the bits into field elements.
        bits.chunks(A::BaseField::size_in_data_bits()).map(Field::from_bits_le).collect()
    }

    /// Returns the recovered data from encoded field elements.
    pub fn decode(plaintext: &[Field<A>]) -> D {
        // Unpack the field elements into bits, and reverse the list to pop the terminus bit off.
        let mut bits =
            plaintext.iter().flat_map(|p| p.to_bits_le()[..A::BaseField::size_in_data_bits()].to_vec()).rev();
        // Remove the terminus bit that was added during encoding.
        while let Some(boolean) = bits.next() {
            // Drop all extraneous `0` bits, in addition to the final `1` bit.
            if boolean.eject_value() {
                // This case will always be reached, since the terminus bit is always `1`.
                break;
            }
        }
        // Reverse the bits back and recover the data from the bits.
        D::from_bits_le(&bits.rev().collect::<Vec<_>>())
    }
}

impl<A: Aleo, D: DataType<A>> TypeName for Data<A, D> {
    fn type_name() -> &'static str {
        "data"
    }
}

// impl<T> Data<T> {
//     /// Encrypts `self` under the given Aleo address and randomizer,
//     /// turning `self` into `Data::Ciphertext(..)` if the `mode` is private.
//     /// Note: The output is guaranteed to satisfy `Data::is_valid(output)`.
//     pub fn encrypt(&mut self, address: Address<A>, randomizer: Scalar<A>) -> Self {
//         match self {
//             Self::Plaintext(data, Mode::Private) => {
//                 // Prepare the plaintext and randomizers as field elements.
//                 let plaintext = data.to_fields();
//                 let randomizers = Hash::hash_many(randomizer * address, plaintext.len());
//                 // Output the ciphertext.
//                 Self::Ciphertext(plaintext.zip_eq(randomizers).map(|(p, r)| p + r).collect(), Mode::Private)
//             },
//             _ => self
//         }
//         // Encrypt the owner, balance, and data.
//         let (record_view_key, owner, balance, data) = {
//             // The number of ciphertext randomizers is set to encrypt the owner, balance, and data.
//             const NUM_RANDOMIZERS: usize = 2 + NUM_DATA_FIELD_ELEMENTS;
//
//             // Construct the plaintext.
//             let mut plaintext = Vec::with_capacity(NUM_RANDOMIZERS);
//             plaintext.push(state.owner().to_group().to_x_coordinate());
//             plaintext.push(state.balance().to_field());
//             plaintext.extend_from_slice(&Self::encode_message(&state.data().to_bits_le()));
//
//             // Ensure the number of plaintext elements is within the number of allowed randomizers.
//             if plaintext.len() > NUM_RANDOMIZERS {
//                 A::halt(format!("Attempted to encrypt {} elements, maximum is {NUM_RANDOMIZERS}", plaintext.len()))
//             } else {
//                 // Pad up to the number of randomizers, if there are less plaintext elements.
//                 plaintext.resize(NUM_RANDOMIZERS, Field::zero());
//             }
//
//             // Compute the record view key.
//             let record_view_key = (state.owner().to_group() * &randomizer).to_x_coordinate();
//             // Compute the randomizers.
//             let randomizers = A::hash_many_psd2(
//                 &[
//                     Field::constant(A::BaseField::from_bytes_le_mod_order(b"AleoEncryption0")),
//                     record_view_key.clone(),
//                 ],
//                 NUM_RANDOMIZERS,
//             );
//
//             // Compute the ciphertext.
//             let ciphertext = plaintext.iter().zip_eq(randomizers).map(|(p, r)| p + r).collect::<Vec<_>>();
//
//             // Prepare the response.
//             let owner = ciphertext[0].clone();
//             let balance = ciphertext[1].clone();
//             let data: [Field<A>; NUM_DATA_FIELD_ELEMENTS] =
//                 [ciphertext[2].clone(), ciphertext[3].clone(), ciphertext[4].clone(), ciphertext[5].clone()];
//
//             (record_view_key, owner, balance, data)
//         };
//
//         // Compute the nonce := G^r.
//         let nonce = A::g_scalar_multiply(&randomizer).to_x_coordinate();
//
//         // Compute the MAC := Hash(G^r^view_key).
//         let mac = A::hash_psd2(&[
//             Field::constant(A::BaseField::from_bytes_le_mod_order(b"AleoMAC0")),
//             record_view_key,
//         ]);
//
//         // Compute the balance commitment := G^state.balance H^r.
//         let bcm = A::commit_ped64(&state.balance().to_bits_le(), &randomizer);
//
//         Self { program: state.program().clone(), owner, balance, data, nonce, mac, bcm }
//     }
//
//     /// Encode a bitstring into a vector of field elements. This is used to convert messages
//     /// to hashable [`Field`] elements.
//     fn encode_message(message: &[Boolean<A>]) -> Vec<Field<A>> {
//         // Add an extra bit to the message.
//         // The final bit serves as a terminus indicator,
//         // and is used during decryption to ensure the length is correct.
//         let mut bits = message.to_vec();
//         bits.push(Boolean::constant(true));
//
//         // Pack the bits into field elements.
//         bits.chunks(A::BaseField::size_in_data_bits()).map(Field::from_bits_le).collect()
//     }
// }
