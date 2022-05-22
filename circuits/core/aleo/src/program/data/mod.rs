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

// mod decrypt;
// mod encrypt;
// mod to_data_id;

use crate::{Aleo, Ciphertext, Entry, Identifier, Plaintext, Visibility};
use snarkvm_circuits_types::{environment::prelude::*, Address, Boolean, Field, Group, Scalar};

use std::collections::HashMap;

pub struct Data<A: Aleo, Private: Visibility<A>>(HashMap<Identifier<A>, Entry<A, Private>>);

// impl<A: Aleo, Private: EntryMode<A>> Data<A, Private> {
//     pub fn new() -> Self {
//         Self(HashMap::new())
//     }
//
//     pub fn insert(&mut self, identifier: Identifier<A>, entry: Entry<A, Private>) {
//         self.0.insert(identifier, entry);
//     }
//
//     pub fn get(&self, identifier: &Identifier<A>) -> Option<&Entry<A, Private>> {
//         self.0.get(identifier)
//     }
//
//     pub fn get_mut(&mut self, identifier: &Identifier<A>) -> Option<&mut Entry<A, Private>> {
//         self.0.get_mut(identifier)
//     }
//
//     pub fn remove(&mut self, identifier: &Identifier<A>) -> Option<Entry<A, Private>> {
//         self.0.remove(identifier)
//     }
//
//     pub fn len(&self) -> usize {
//         self.0.len()
//     }
//
//     pub fn is_empty(&self) -> bool {
//         self.0.is_empty()
//     }
//
//     pub fn iter(&self) -> impl Iterator<Item = (&Identifier<A>, &Entry<A, Private>)> {
//         self.0.iter()
//     }
//
//     pub fn iter_mut(&mut self) -> impl Iterator<Item = (&Identifier<A>, &mut Entry<A, Private>)> {
//         self.0.iter_mut()
//     }
//
//     pub fn keys(&self) -> impl Iterator<Item = &Identifier<A>> {
//         self.0.keys()
//     }
//
//     pub fn values(&self) -> impl Iterator<Item = &Entry<A, Private>> {
//         self.0.values()
//     }
//
//     pub fn values_mut(&mut self) -> impl Iterator<Item = &mut Entry<A, Private>> {
//         self.0.values_mut()
//     }
//
//     pub fn clear(&mut self) {
//         self.0.clear();
//     }
// }

// impl<A: Aleo> Data<A, Plaintext<A>> {
//     /// Encrypts `self` under the given Aleo address and randomizer.
//     pub fn encrypt(&self, address: Address<A>, randomizer: Scalar<A>) -> Data<A, Ciphertext<A>> {
//         // self.0.iter().map(|(identifier, entry)| {
//         //     identifier.to_bits_le().iter().chain(entry.)
//         // })
//
//         // Only encrypt the `Data` entries that are `Entry::Private`.
//         self.0.values().map(|entry| {
//             match entry {
//                 Entry::Constant(..) | Entry::Public(..) => entry,
//                 Entry::Private(entry) => {
//                     // Encrypt the entry.
//                     entry
//                     // Entry::Private(Ciphertext::new(literal_type, ciphertext))
//                 }
//             }
//         })
//
//         match self {
//             Self::Plaintext(data, Mode::Private) => {
//                 // Encode the data as field elements.
//                 let plaintext = Self::encode(data);
//                 // Compute the data view key.
//                 let data_view_key = (address.to_group() * randomizer).to_x_coordinate();
//                 // Prepare a randomizer for each field element.
//                 let randomizers = A::hash_many_psd8(&[A::encryption_domain(), data_view_key], plaintext.len());
//                 // Compute the ciphertext field elements.
//                 let ciphertext = plaintext.iter().zip_eq(randomizers).map(|(p, r)| p + r).collect();
//                 // Output the ciphertext.
//                 Self::Ciphertext(ciphertext, Mode::Private)
//             }
//             _ => (*self).clone(),
//         }
//     }
//
//     /// Returns a list of field elements encoding the given data.
//     pub(super) fn encode(data: &D) -> Vec<Field<A>> {
//         // Encode the data as little-endian bits.
//         let mut bits = data.to_bits_le();
//         // Adds one final bit to the data, to serve as a terminus indicator.
//         // During decryption, this final bit ensures we've reached the end.
//         bits.push(Boolean::constant(true));
//         // Pack the bits into field elements.
//         bits.chunks(A::BaseField::size_in_data_bits()).map(Field::from_bits_le).collect()
//     }
//
//     /// Returns the recovered data from encoded field elements.
//     pub(super) fn decode(plaintext: &[Field<A>]) -> D {
//         // Unpack the field elements into bits, and reverse the list to pop the terminus bit off.
//         let mut bits =
//             plaintext.iter().flat_map(|p| p.to_bits_le()[..A::BaseField::size_in_data_bits()].to_vec()).rev();
//         // Remove the terminus bit that was added during encoding.
//         for boolean in bits.by_ref() {
//             // Drop all extraneous `0` bits, in addition to the final `1` bit.
//             if boolean.eject_value() {
//                 // This case will always be reached, since the terminus bit is always `1`.
//                 break;
//             }
//         }
//         // Reverse the bits back and recover the data from the bits.
//         D::from_bits_le(&bits.rev().collect::<Vec<_>>())
//     }
// }

// /// A general purpose data structure for representing program data in a record.
// pub trait DataType<A: Aleo>: Clone + Eject + ToBits<Boolean = Boolean<A>> + FromBits<Boolean = Boolean<A>> {}
//
// #[derive(Clone)]
// pub enum Data<A: Aleo, Private: EntryMode<A>> {
//     /// Publicly-visible data.
//     Plaintext(D, Mode),
//     /// Private data encrypted under the account owner's address.
//     Ciphertext(Vec<Field<A>>, Mode),
// }
//
// impl<A: Aleo, Private: EntryMode<A>> Data<A, D> {
//     /// Returns the mode of the data.
//     pub fn mode(&self) -> Mode {
//         match self {
//             Self::Plaintext(_, mode) => *mode,
//             Self::Ciphertext(_, mode) => *mode,
//         }
//     }
//
//     /// Returns `true` if the enum variant corresponds to the correct mode.
//     /// Otherwise, the method returns `false`.
//     pub fn is_valid(&self) -> bool {
//         match self {
//             Self::Plaintext(_, mode) => mode.is_constant() || mode.is_public(),
//             Self::Ciphertext(_, mode) => mode.is_private(),
//         }
//     }
// }
//
// impl<A: Aleo, Private: EntryMode<A>> TypeName for Data<A, D> {
//     fn type_name() -> &'static str {
//         "data"
//     }
// }
