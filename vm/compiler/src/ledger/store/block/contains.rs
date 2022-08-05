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

impl<N: Network, B: BlockStorage<N>, T: TransactionStorage<N>> BlockStore<N, B, T> {
    /// Returns `true` if the given state root exists.
    pub fn contains_state_root(&self, state_root: &Field<N>) -> bool {
        state_root == self.latest_state_root()
            || self.headers.values().any(|h| Header::previous_state_root(&h) == state_root)
    }

    /// Returns `true` if the given block hash exists.
    pub fn contains_block_hash(&self, block_hash: &N::BlockHash) -> bool {
        self.current_hash == *block_hash || self.hashes.values().any(|hash| *hash == *block_hash)
    }

    /// Returns `true` if the given block height exists.
    pub fn contains_height(&self, height: u32) -> Result<bool> {
        self.hashes.contains_key(&height)
    }

    /// Returns `true` if the given transaction exists.
    pub fn contains_transaction(&self, transaction: &Transaction<N>) -> Result<bool> {
        self.contains_transaction_id(&transaction.id())
    }

    /// Returns `true` if the given transaction ID exists.
    pub fn contains_transaction_id(&self, transaction_id: &N::TransactionID) -> Result<bool> {
        self.transaction_store.contains_transaction_id(transaction_id)
    }

    /// Returns `true` if the given transition exists.
    pub fn contains_transition(&self, transition: &Transition<N>) -> Result<bool> {
        self.contains_transition_id(transition.id())
    }

    /// Returns `true` if the given transition ID exists.
    pub fn contains_transition_id(&self, transition_id: &N::TransitionID) -> Result<bool> {
        self.transaction_store.contains_transition_id(transition_id)
    }

    /// Returns `true` if the given transition public key exists.
    pub fn contains_transition_public_key(&self, tpk: &Group<N>) -> Result<bool> {
        self.transaction_store.contains_transition_public_key(tpk)
    }

    /// Returns `true` if the given serial number exists.
    pub fn contains_serial_number(&self, serial_number: &Field<N>) -> Result<bool> {
        self.transaction_store.contains_serial_number(serial_number)
    }

    /// Returns `true` if the given commitment exists.
    pub fn contains_commitment(&self, commitment: &Field<N>) -> Result<bool> {
        self.transaction_store.contains_commitment(commitment)
    }

    /// Returns `true` if the given nonce exists.
    pub fn contains_nonce(&self, nonce: &Group<N>) -> Result<bool> {
        self.transaction_store.contains_nonce(nonce)
    }
}
