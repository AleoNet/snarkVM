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

mod decrypt;
mod encrypt;
// mod to_data_id;

use crate::{Aleo, Ciphertext, Entry, Identifier, Plaintext, Visibility};
use snarkvm_circuits_types::{environment::prelude::*, Address, Boolean, Field, Group, Scalar};

pub struct Data<A: Aleo, Private: Visibility<A>>(Vec<(Identifier<A>, Entry<A, Private>)>);

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
