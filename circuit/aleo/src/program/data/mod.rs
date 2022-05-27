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
// use snarkvm_circuit_types::environment::assert_scope;

mod ciphertext;
pub use ciphertext::Ciphertext;

mod entry;
pub use entry::Entry;

mod identifier;
pub use identifier::Identifier;

mod literal;
pub use literal::Literal;

mod plaintext;
pub use plaintext::Plaintext;

mod decrypt;
mod encrypt;
// mod to_data_id;

use crate::ViewKey;
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Address, Boolean, Group, Scalar};

pub trait Visibility<A: Aleo>: ToBits<Boolean = Boolean<A>> + FromBits + ToFields + FromFields {
    /// Returns the number of field elements to encode `self`.
    fn size_in_fields(&self) -> u16;
}

pub struct Data<A: Aleo, Private: Visibility<A>>(Vec<(Identifier<A>, Entry<A, Private>)>);

#[cfg(console)]
impl<A: Aleo> Eject for Data<A, Plaintext<A>> {
    type Primitive = console::Data<A::Network, console::Plaintext<A::Network>>;

    /// Ejects the mode of the data.
    fn eject_mode(&self) -> Mode {
        self.0.iter().map(|(identifier, entry)| (identifier, entry).eject_mode()).collect::<Vec<_>>().eject_mode()
    }

    /// Ejects the data.
    fn eject_value(&self) -> Self::Primitive {
        console::Data::from(
            self.0.iter().map(|(identifier, entry)| (identifier, entry).eject_value()).collect::<Vec<_>>(),
        )
    }
}

#[cfg(console)]
impl<A: Aleo, Private: Visibility<A>> TypeName for Data<A, Private> {
    fn type_name() -> &'static str {
        "data"
    }
}

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
