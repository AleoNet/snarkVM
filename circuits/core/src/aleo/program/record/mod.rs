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
mod is_owner;
mod to_record_id;

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
