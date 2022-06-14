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

mod serial_number;
pub use serial_number::SerialNumber;

mod decrypt;
mod encrypt;
mod is_owner;
mod to_bits;
mod to_commitment;
mod to_record_view_key;
mod to_serial_number;

use crate::State;
use snarkvm_console_account::{Address, ViewKey};
use snarkvm_console_network::Network;
use snarkvm_console_types::prelude::*;

/// A program record is a set of **ciphertext** variables used by a program.
/// Note: `Record` is the **encrypted** form of `State`.
#[derive(Clone)]
pub struct Record<N: Network> {
    /// The **encrypted** address this record belongs to (i.e. `owner + HashMany(G^r^view_key, 2)[0]`).
    owner: Field<N>,
    /// The **encrypted** balance in this record (i.e. `balance.to_field() + HashMany(G^r^view_key, 2)[1]`).
    balance: Field<N>,
    /// The data ID of this record.
    data: Field<N>,
    /// The nonce for this record (i.e. `G^r`).
    nonce: Group<N>,
    /// The MAC for this record (i.e. `Hash(G^r^view_key)`).
    mac: Field<N>,
    /// The balance commitment for this record (i.e. `G^balance H^HashToScalar(G^r^view_key)`).
    bcm: Group<N>,
}

impl<N: Network> Record<N> {
    /// Initializes a new record.
    pub fn new(
        owner: Field<N>,
        balance: Field<N>,
        data: Field<N>,
        nonce: Group<N>,
        mac: Field<N>,
        bcm: Group<N>,
    ) -> Self {
        Self { owner, balance, data, nonce, mac, bcm }
    }

    /// Returns the **encrypted** address this record belongs to.
    /// Note: `owner` is the **encrypted** form of `State::owner`.
    pub const fn owner(&self) -> Field<N> {
        self.owner
    }

    /// Returns the **encrypted** balance in this record.
    /// Note: `balance` is the **encrypted** form of `State::balance`.
    pub const fn balance(&self) -> Field<N> {
        self.balance
    }

    /// Returns the program data.
    pub const fn data(&self) -> Field<N> {
        self.data
    }

    /// Returns the nonce for this record.
    pub const fn nonce(&self) -> Group<N> {
        self.nonce
    }

    /// Returns the MAC for this record.
    pub const fn mac(&self) -> Field<N> {
        self.mac
    }

    /// Returns the balance commitment for this record.
    pub const fn bcm(&self) -> Group<N> {
        self.bcm
    }
}
