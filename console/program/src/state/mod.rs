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

mod decrypt;
mod encrypt;
mod to_commitment;
mod to_serial_number;

mod serial_number;
pub use serial_number::SerialNumber;

use crate::{Ciphertext, Data, Record};
use snarkvm_console_account::{Address, PrivateKey, ViewKey};
use snarkvm_console_network::Network;
use snarkvm_curves::AffineCurve;
use snarkvm_utilities::ToBits;

use anyhow::Result;

/// A program's state is a set of **plaintext** variables used by a program.
/// Note: `State` is the **decrypted** form of `Record`.
pub struct State<N: Network> {
    /// The program ID of the record.
    program: N::Field,
    /// The process ID of the record.
    process: N::Field,
    /// The Aleo address this state belongs to.
    owner: Address<N>,
    /// The account balance in this program state.
    balance: u64,
    /// The data for this program state.
    data: Data<N, Ciphertext<N>>,
    /// The nonce for this program state (i.e. `G^r`).
    nonce: N::Affine,
}

impl<N: Network> State<N> {
    /// Initializes a new instance of `State`.
    pub fn new(
        program: N::Field,
        process: N::Field,
        owner: Address<N>,
        balance: u64,
        data: Data<N, Ciphertext<N>>,
        nonce: N::Affine,
    ) -> Self {
        Self { program, process, owner, balance, data, nonce }
    }

    /// Returns the program ID.
    pub const fn program(&self) -> N::Field {
        self.program
    }

    /// Returns the process ID.
    pub const fn process(&self) -> N::Field {
        self.process
    }

    /// Returns the account owner.
    pub const fn owner(&self) -> &Address<N> {
        &self.owner
    }

    /// Returns the account balance.
    pub const fn balance(&self) -> &u64 {
        &self.balance
    }

    /// Returns the program data.
    pub const fn data(&self) -> &Data<N, Ciphertext<N>> {
        &self.data
    }

    /// Returns the nonce for this program state.
    pub const fn nonce(&self) -> &N::Affine {
        &self.nonce
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
