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

mod randomizer;
pub use randomizer::Randomizer;

mod decrypt;
mod encrypt;

use crate::Record;
use snarkvm_circuit_account::ViewKey;
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Address, Field, Group, Scalar, U64};

// TODO (howardwu): Check mode is only public/private, not constant.
/// A program's state is a set of **plaintext** variables used by a program.
/// Note: `State` is the **decrypted** form of `Record`.
pub struct State<A: Aleo> {
    /// The Aleo address this state belongs to.
    owner: Address<A>,
    /// The account balance in this program state.
    balance: U64<A>,
    /// The data ID for this program state.
    data: Field<A>,
    /// The nonce for this program state (i.e. `G^r`).
    nonce: Group<A>,
}

#[cfg(console)]
impl<A: Aleo> Inject for State<A> {
    type Primitive = console::State<A::Network>;

    /// Initializes a state from the given mode and native state.
    fn new(mode: Mode, state: Self::Primitive) -> State<A> {
        // Return the state.
        Self {
            owner: Address::new(mode, state.owner()),
            balance: U64::new(mode, state.balance()),
            data: Field::new(mode, state.data()),
            nonce: Group::new(mode, state.nonce()),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for State<A> {
    type Primitive = console::State<A::Network>;

    /// Ejects the mode of the state.
    fn eject_mode(&self) -> Mode {
        (&self.owner, &self.balance, &self.data, &self.nonce).eject_mode()
    }

    /// Ejects the state.
    fn eject_value(&self) -> Self::Primitive {
        Self::Primitive::new(
            self.owner.eject_value(),
            *self.balance.eject_value(),
            self.data.eject_value(),
            self.nonce.eject_value(),
        )
    }
}

impl<A: Aleo> From<(Address<A>, U64<A>, Field<A>, Group<A>)> for State<A> {
    /// Initializes a new `State` from the given parameters.
    fn from((owner, balance, data, nonce): (Address<A>, U64<A>, Field<A>, Group<A>)) -> Self {
        Self { owner, balance, data, nonce }
    }
}

impl<A: Aleo> State<A> {
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
    pub fn nonce(&self) -> &Group<A> {
        &self.nonce
    }
}

#[cfg(console)]
impl<A: Aleo> TypeName for State<A> {
    fn type_name() -> &'static str {
        "state"
    }
}
