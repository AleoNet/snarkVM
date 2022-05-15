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

mod encrypt;
mod to_commitment;

use crate::aleo::{Aleo, Record, Scalar};
use snarkvm_circuits_types::{environment::prelude::*, Address, Field, U64};

// TODO (howardwu): Check mode is only public/private, not constant.
/// A program's state is a set of **plaintext** variables used by a program.
/// Note: `State` is the **decrypted** form of `Record`.
pub struct State<A: Aleo> {
    /// The program this state belongs to.
    program: Field<A>,
    /// The Aleo address this state belongs to.
    owner: Address<A>,
    /// The account balance in this program state.
    balance: U64<A>,
    /// The ID for the program data.
    data: Field<A>,
    /// The nonce for this program state (i.e. `G^r`).
    nonce: Field<A>,
}

impl<A: Aleo> From<(Field<A>, Address<A>, U64<A>, Field<A>, Field<A>)> for State<A> {
    #[inline]
    fn from((program, owner, balance, data, nonce): (Field<A>, Address<A>, U64<A>, Field<A>, Field<A>)) -> Self {
        Self { program, owner, balance, data, nonce }
    }
}

impl<A: Aleo> State<A> {
    /// Returns the program ID.
    pub fn program(&self) -> &Field<A> {
        &self.program
    }

    /// Returns the account owner.
    pub fn owner(&self) -> &Address<A> {
        &self.owner
    }

    /// Returns the account balance.
    pub fn balance(&self) -> &U64<A> {
        &self.balance
    }

    /// Returns the program data ID.
    pub fn data(&self) -> &Field<A> {
        &self.data
    }

    /// Returns the nonce for this program state.
    pub fn nonce(&self) -> &Field<A> {
        &self.nonce
    }
}

impl<A: Aleo> TypeName for State<A> {
    fn type_name() -> &'static str {
        "state"
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::aleo::Devnet as Circuit;
//     use snarkvm_circuits_types::Group;
//
//     #[test]
//     fn test_state() {
//         let first = Literal::<Circuit>::from_str("10field.public");
//         let second = Literal::from_str("true.private");
//         let third = Literal::from_str("99i64.public");
//
//         let _candidate = State::<Circuit> {
//             owner: Address::from(Group::from_str("2group.private")),
//             balance: U64::from_str("1u64.private"),
//             data: vec![first, second, third],
//         };
//     }
// }
