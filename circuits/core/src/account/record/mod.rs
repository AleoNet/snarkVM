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

#[cfg(test)]
use snarkvm_circuits_types::environment::assert_scope;

pub mod ciphertext;
pub use ciphertext::*;

use crate::Aleo;
use snarkvm_circuits_types::{environment::prelude::*, Address, Field, Literal, I64, U8};

// TODO (howardwu): Check mode is only public/private, not constant.
#[derive(Debug, Clone)]
pub struct Record<A: Aleo> {
    // /// The program this record belongs to.
    // program: Field<A>,
    // /// The Aleo address this record belongs to.
    // owner: Data<Address<A>>,
    // /// The balance of Aleo credits in this record.
    // balance: Data<U64<A>>,
    // /// The data in this record.
    // data: Vec<Data<Value>>,
    // /// The nonce for this record.
    // nonce: Field<A>
    owner: Address<A>,
    value: I64<A>,
    payload: Vec<U8<A>>,
    view_key: Field<A>,
    ciphertext: Ciphertext<A>,
    data: Vec<Literal<A>>,
}

impl<A: Aleo> Record<A> {
    /// Returns a new instance of a record.
    pub fn new(
        owner: Address<A>,
        value: I64<A>,
        payload: Vec<U8<A>>,
        view_key: Field<A>,
        ciphertext: Ciphertext<A>,
        data: Vec<Literal<A>>,
    ) -> Self {
        Self { owner, value, payload, view_key, ciphertext, data }
    }

    /// Returns the record owner.
    pub fn owner(&self) -> &Address<A> {
        &self.owner
    }

    /// Returns the record balance.
    pub fn balance(&self) -> &I64<A> {
        &self.value
    }

    /// Returns the record payload.
    pub fn payload(&self) -> &Vec<U8<A>> {
        &self.payload
    }

    /// Returns the record view key.
    pub fn view_key(&self) -> &Field<A> {
        &self.view_key
    }

    /// Returns the record ciphertext.
    pub fn ciphertext(&self) -> &Ciphertext<A> {
        &self.ciphertext
    }

    /// Returns the record data.
    pub fn data(&self) -> &Vec<Literal<A>> {
        &self.data
    }
}

impl<A: Aleo> TypeName for Record<A> {
    fn type_name() -> &'static str {
        "record"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Devnet as Circuit;
    use snarkvm_circuits_types::Group;

    #[test]
    fn test_record() {
        let first = Literal::<Circuit>::from_str("10field.public");
        let second = Literal::from_str("true.private");
        let third = Literal::from_str("99i64.public");

        let _candidate = Record::<Circuit> {
            owner: Address::from(Group::from_str("2group.private")),
            value: I64::from_str("1i64.private"),
            payload: vec![U8::from_str("1u8.private")],
            view_key: Field::from_str("1field.private"),
            ciphertext: Ciphertext::new(
                Mode::Private,
                (
                    Default::default(),
                    Default::default(),
                    Default::default(),
                    vec![Default::default()],
                    Default::default(),
                    true,
                ),
            ),
            data: vec![first, second, third],
        };
    }
}
