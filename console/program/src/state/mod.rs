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

use crate::{Data, Plaintext, Record};
use snarkvm_console_account::{Address, ViewKey};
use snarkvm_console_network::Network;
use snarkvm_curves::AffineCurve;
use snarkvm_utilities::ToBits;

use anyhow::Result;

/// A program's state is a set of **plaintext** variables used by a program.
/// Note: `State` is the **decrypted** form of `Record`.
pub struct State<N: Network> {
    /// The Aleo address this state belongs to.
    owner: Address<N>,
    /// The account balance in this program state.
    balance: u64,
    /// The data for this program state.
    data: Data<N, Plaintext<N>>,
    /// The nonce for this program state (i.e. `G^r`).
    nonce: N::Affine,
}

impl<N: Network> From<(Address<N>, u64, Data<N, Plaintext<N>>, N::Affine)> for State<N> {
    #[inline]
    fn from((owner, balance, data, nonce): (Address<N>, u64, Data<N, Plaintext<N>>, N::Affine)) -> Self {
        Self { owner, balance, data, nonce }
    }
}

impl<N: Network> State<N> {
    /// Returns the record corresponding to the state.
    pub fn encrypt(&self, randomizer: &N::Scalar) -> Result<Record<N>> {
        Record::encrypt(self, randomizer)
    }

    /// Initializes a new instance of `State` given a record and view key.
    pub fn decrypt(record: &Record<N>, view_key: &ViewKey<N>) -> Result<Self> {
        record.decrypt(view_key)
    }

    /// Returns the program state commitment, given the program ID, process ID, and data ID.
    pub fn to_commitment(&self, program: N::Field, process: N::Field, data: N::Field) -> Result<N::Field> {
        // Retrieve the x-coordinate of the owner.
        let owner = self.owner.to_x_coordinate();
        // Convert the balance into a field element.
        let balance = N::Field::from(self.balance as u128);
        // Retrieve the x-coordinate of the nonce.
        let nonce = self.nonce.to_x_coordinate();
        // Compute the BHP hash of the program state.
        N::hash_bhp1024(&[program, process, owner, balance, data, nonce].to_bits_le())
    }

    /// Returns the account owner.
    pub const fn owner(&self) -> &Address<N> {
        &self.owner
    }

    /// Returns the account balance.
    pub const fn balance(&self) -> &u64 {
        &self.balance
    }

    /// Returns the program data ID.
    pub const fn data(&self) -> &Data<N, Plaintext<N>> {
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
