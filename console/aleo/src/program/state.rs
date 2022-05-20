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

use crate::{Address, Network, Record, ViewKey};
use snarkvm_curves::AffineCurve;
use snarkvm_utilities::ToBits;

use anyhow::Result;

// TODO (howardwu): Check mode is only public/private, not constant.
/// A program's state is a set of **plaintext** variables used by a program.
/// Note: `State` is the **decrypted** form of `Record`.
pub struct State<N: Network> {
    /// The program this state belongs to.
    program: N::Field,
    /// The Aleo address this state belongs to.
    owner: Address<N>,
    /// The account balance in this program state.
    balance: u64,
    /// The ID for the program data.
    data: N::Field,
    /// The nonce for this program state (i.e. `G^r`).
    nonce: N::Affine,
}

impl<N: Network> From<(N::Field, Address<N>, u64, N::Field, N::Affine)> for State<N> {
    #[inline]
    fn from((program, owner, balance, data, nonce): (N::Field, Address<N>, u64, N::Field, N::Affine)) -> Self {
        Self { program, owner, balance, data, nonce }
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

    /// Returns the program state commitment.
    pub fn to_commitment(&self) -> Result<N::Field> {
        // Retrieve the x-coordinate of the owner.
        let owner = self.owner.to_x_coordinate();
        // Convert the balance into a field element.
        let balance = N::Field::from(self.balance as u128);
        // TODO (howardwu): Abstraction - add support for a custom BHP hash size.
        // Compute the BHP hash of the program state.
        let left = N::hash_bhp1024(&[self.program, owner, balance, self.data].to_bits_le())?;
        let right = N::hash_bhp1024(&[self.nonce.to_x_coordinate()].to_bits_le())?;
        N::hash_bhp512(&[left, right].to_bits_le())
    }

    /// Returns the program ID.
    pub const fn program(&self) -> &N::Field {
        &self.program
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
    pub const fn data(&self) -> &N::Field {
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
