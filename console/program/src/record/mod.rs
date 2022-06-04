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
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_utilities::{CryptoRng, Rng, ToBits, ToBytes};

use anyhow::{ensure, Result};

/// A program's record is a set of **ciphertext** variables used by a program.
/// Note: `Record` is the **encrypted** form of `State`.
#[derive(Clone)]
pub struct Record<N: Network> {
    /// The program ID of this record.
    program: N::Field,
    /// The process ID of this record.
    process: N::Field,
    /// The **encrypted** address this record belongs to (i.e. `owner + HashMany(G^r^view_key, 2)[0]`).
    owner: N::Field,
    /// The **encrypted** balance in this record (i.e. `balance.to_field() + HashMany(G^r^view_key, 2)[1]`).
    balance: N::Field,
    /// The data ID of this record.
    data: N::Field,
    /// The nonce for this record (i.e. `G^r`).
    nonce: N::Affine,
    /// The MAC for this record (i.e. `Hash(G^r^view_key)`).
    mac: N::Field,
    /// The balance commitment for this record (i.e. `G^balance H^HashToScalar(G^r^view_key)`).
    bcm: N::Affine,
}

impl<N: Network> Record<N> {
    /// Initializes a new record.
    pub fn new(
        program: N::Field,
        process: N::Field,
        owner: N::Field,
        balance: N::Field,
        data: N::Field,
        nonce: N::Affine,
        mac: N::Field,
        bcm: N::Affine,
    ) -> Self {
        Self { program, process, owner, balance, data, nonce, mac, bcm }
    }

    /// Returns the program ID of the record.
    pub const fn program(&self) -> N::Field {
        self.program
    }

    /// Returns the process ID of the record.
    pub const fn process(&self) -> N::Field {
        self.process
    }

    /// Returns the **encrypted** address this record belongs to.
    /// Note: `owner` is the **encrypted** form of `State::owner`.
    pub const fn owner(&self) -> N::Field {
        self.owner
    }

    /// Returns the **encrypted** balance in this record.
    /// Note: `balance` is the **encrypted** form of `State::balance`.
    pub const fn balance(&self) -> N::Field {
        self.balance
    }

    /// Returns the program data.
    pub const fn data(&self) -> N::Field {
        self.data
    }

    /// Returns the nonce for this record.
    pub const fn nonce(&self) -> N::Affine {
        self.nonce
    }

    /// Returns the MAC for this record.
    pub const fn mac(&self) -> N::Field {
        self.mac
    }

    /// Returns the balance commitment for this record.
    pub const fn bcm(&self) -> N::Affine {
        self.bcm
    }
}
