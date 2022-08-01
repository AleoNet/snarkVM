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

use super::*;

impl<
    N: Network,
    PreviousHashesMap: for<'a> Map<'a, u32, N::BlockHash>,
    HeadersMap: for<'a> Map<'a, u32, Header<N>>,
    TransactionsMap: for<'a> Map<'a, u32, Transactions<N>>,
    SignatureMap: for<'a> Map<'a, u32, Signature<N>>,
    ProgramsMap: for<'a> Map<'a, ProgramID<N>, Deployment<N>>,
> Ledger<N, PreviousHashesMap, HeadersMap, TransactionsMap, SignatureMap, ProgramsMap>
{
    /// Returns `true` if the given state root exists.
    pub fn contains_state_root(&self, state_root: &Field<N>) -> bool {
        state_root == self.latest_state_root()
            || self.headers.values().map(Header::previous_state_root).any(|root| root == state_root)
    }

    /// Returns `true` if the given block hash exists.
    pub fn contains_block_hash(&self, block_hash: &N::BlockHash) -> bool {
        self.current_hash == *block_hash || self.previous_hashes.values().any(|hash| *hash == *block_hash)
    }

    /// Returns `true` if the given block height exists.
    pub fn contains_height(&self, height: u32) -> Result<bool> {
        self.previous_hashes
            .contains_key(&height)
            .or_else(|_| self.headers.contains_key(&height))
            .or_else(|_| self.transactions.contains_key(&height))
    }

    /// Returns `true` if the given transaction exists.
    pub fn contains_transaction(&self, transaction: &Transaction<N>) -> bool {
        self.transaction_ids().contains(&transaction.id())
    }

    /// Returns `true` if the given transaction ID exists.
    pub fn contains_transaction_id(&self, transaction_id: &N::TransactionID) -> bool {
        self.transaction_ids().contains(transaction_id)
    }

    /// Returns `true` if the given transition exists.
    pub fn contains_transition(&self, transition: &Transition<N>) -> bool {
        self.transition_ids().contains(transition.id())
    }

    /// Returns `true` if the given transition ID exists.
    pub fn contains_transition_id(&self, transition_id: &N::TransitionID) -> bool {
        self.transition_ids().contains(transition_id)
    }

    /// Returns `true` if the given transition public key exists.
    pub fn contains_transition_public_key(&self, tpk: &Group<N>) -> bool {
        self.transition_public_keys().contains(tpk)
    }

    /// Returns `true` if the given serial number exists.
    pub fn contains_serial_number(&self, serial_number: &Field<N>) -> bool {
        self.serial_numbers().contains(serial_number)
    }

    /// Returns `true` if the given commitment exists.
    pub fn contains_commitment(&self, commitment: &Field<N>) -> bool {
        self.commitments().contains(commitment)
    }

    /// Returns `true` if the given nonce exists.
    pub fn contains_nonce(&self, nonce: &Group<N>) -> bool {
        self.nonces().contains(nonce)
    }
}
