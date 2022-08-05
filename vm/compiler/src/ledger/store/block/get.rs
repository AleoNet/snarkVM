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

use crate::ledger::{OutputRecordsFilter, Transactions, ViewKey};

use std::borrow::Cow;

impl<N: Network, B: BlockStorage<N>, T: TransactionStorage<N>> BlockStore<N, B, T> {
    /// Returns the block for the given block height.
    pub fn get_block(&self, height: u32) -> Result<Block<N>> {
        Block::from(
            self.get_previous_hash(height)?,
            *self.get_header(height)?,
            self.get_transactions(height)?.into_owned(),
            *self.get_signature(height)?,
        )
    }

    /// Returns the block for the given block hash.
    pub fn get_block_from_hash(&self, hash: N::BlockHash) -> Result<Block<N>> {
        self.get_block(self.get_block_height(hash)?)
    }

    /// Returns the block hash for the given block height.
    pub fn get_hash(&self, height: u32) -> Result<N::BlockHash> {
        match height.cmp(&self.current_height) {
            Ordering::Equal => Ok(self.current_hash),
            Ordering::Less => match self.hashes.get(&height)? {
                Some(block_hash) => Ok(*block_hash),
                None => bail!("Missing block hash for block {height}"),
            },
            Ordering::Greater => bail!("Block {height} (given) is greater than the current height"),
        }
    }

    /// Returns the previous block hash for the given block height.
    pub fn get_previous_hash(&self, height: u32) -> Result<N::BlockHash> {
        match height {
            0 => Ok(N::BlockHash::default()),
            height => self.get_hash(height.saturating_sub(1)),
        }
    }

    /// Returns the block height for the given block hash.
    pub fn get_block_height(&self, hash: N::BlockHash) -> Result<u32> {
        match self.headers.get(&hash)? {
            Some(header) => Ok(header.metadata().height()),
            None => bail!("Missing block header for block hash {hash}"),
        }
    }

    /// Returns the block header for the given block height.
    pub fn get_header(&self, height: u32) -> Result<Cow<'_, Header<N>>> {
        match self.headers.get(&*self.get_hash(height)?)? {
            Some(header) => Ok(header),
            None => bail!("Missing block header for block {height}"),
        }
    }

    /// Returns the block transactions for the given block height.
    pub fn get_transactions(&self, height: u32) -> Result<Cow<'_, Transactions<N>>> {
        match self.transactions.get(&*self.get_hash(height)?)? {
            Some(transaction_ids) => transaction_ids
                .iter()
                .map(|transaction_id| self.transaction_store.get_transaction(*transaction_id))
                .collect::<Result<Vec<_>>>()
                .map(|transactions| Cow::Owned(Transactions::from(&transactions))),
            None => bail!("Missing block transactions for block {height}"),
        }
    }

    /// Returns the block signature for the given block height.
    pub fn get_signature(&self, height: u32) -> Result<Cow<'_, Signature<N>>> {
        match self.signatures.get(&*self.get_hash(height)?)? {
            Some(signature) => Ok(signature),
            None => bail!("Missing signature for block {height}"),
        }
    }

    /// Returns the transaction for the given transaction id.
    pub fn get_transaction(&self, transaction_id: N::TransactionID) -> Result<Transaction<N>> {
        self.transaction_store.get_transaction(transaction_id)
    }

    /// Returns the transactions for the given transition id.
    pub fn get_transition(&self, transition_id: N::TransitionID) -> Result<Cow<'_, Transition<N>>> {
        self.transaction_store.get_transition(transition_id)
    }

    /// Returns the output records that belong to the given view key.
    pub fn get_output_records<'a>(
        &'a self,
        view_key: &'a ViewKey<N>,
        filter: OutputRecordsFilter<N>,
    ) -> impl '_ + Iterator<Item = (Field<N>, Record<N, Plaintext<N>>)> {
        self.transaction_store.get_output_records(view_key, filter)
    }
}
