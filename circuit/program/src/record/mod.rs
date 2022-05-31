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
use snarkvm_circuit_types::environment::assert_scope;

mod decrypt;
mod encrypt;
mod equal;
mod is_owner;
mod to_commitment;

use crate::State;
use snarkvm_circuit_account::ViewKey;
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Address, Boolean, Field, Group, U64};

// TODO (howardwu): Check mode is only public/private, not constant.
/// A program's record is a set of **ciphertext** variables used by a program.
/// Note: `Record` is the **encrypted** form of `State`.
pub struct Record<A: Aleo> {
    /// The program this record belongs to.
    program: Field<A>,
    /// The process this record corresponds to.
    process: Field<A>,
    /// The **encrypted** address this record belongs to (i.e. `owner + HashMany(G^r^view_key, 2)[0]`).
    owner: Field<A>,
    /// The **encrypted** balance in this record (i.e. `balance.to_field() + HashMany(G^r^view_key, 2)[1]`).
    balance: Field<A>,
    /// The ID for the program data.
    data: Field<A>,
    /// The nonce for this record (i.e. `G^r`).
    nonce: Group<A>,
    /// The MAC for this record (i.e. `Hash(G^r^view_key)`).
    mac: Field<A>,
    /// The balance commitment for this record (i.e. `G^balance H^HashToScalar(G^r^view_key)`).
    bcm: Field<A>,
}

#[cfg(console)]
impl<A: Aleo> Inject for Record<A> {
    type Primitive = console::Record<A::Network>;

    /// Initializes a record from the given mode and native record.
    fn new(mode: Mode, record: Self::Primitive) -> Record<A> {
        // Return the record.
        Self {
            program: Field::new(mode, record.program()),
            process: Field::new(mode, record.process()),
            owner: Field::new(mode, record.owner()),
            balance: Field::new(mode, record.balance()),
            data: Field::new(mode, record.data()),
            nonce: Group::new(mode, record.nonce()),
            mac: Field::new(mode, record.mac()),
            bcm: Field::new(mode, record.bcm()),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for Record<A> {
    type Primitive = console::Record<A::Network>;

    /// Ejects the mode of the record.
    fn eject_mode(&self) -> Mode {
        (&self.program, &self.process, &self.owner, &self.balance, &self.data, &self.nonce, &self.mac, &self.bcm)
            .eject_mode()
    }

    /// Ejects the record.
    fn eject_value(&self) -> Self::Primitive {
        Self::Primitive::new(
            self.program.eject_value(),
            self.process.eject_value(),
            self.owner.eject_value(),
            self.balance.eject_value(),
            self.data.eject_value(),
            self.nonce.eject_value(),
            self.mac.eject_value(),
            self.bcm.eject_value(),
        )
    }
}

#[cfg(console)]
impl<A: Aleo> TypeName for Record<A> {
    fn type_name() -> &'static str {
        "record"
    }
}
