// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::prelude::*;

use anyhow::{anyhow, Result};
use chrono::Utc;
use rand::{CryptoRng, Rng};
use std::collections::HashSet;

#[derive(Clone, Debug)]
pub struct Ledger<N: Network> {
    /// The canonical chain of blocks.
    canon_blocks: Blocks<N>,
    /// The set of unknown orphan blocks.
    orphan_blocks: HashSet<Block<N>>,
    /// The pool of unconfirmed transactions.
    memory_pool: MemoryPool<N>,
}

impl<N: Network> Ledger<N> {
    /// Initializes a new instance of the ledger.
    pub fn new() -> Result<Self> {
        Ok(Self {
            canon_blocks: Blocks::new()?,
            orphan_blocks: Default::default(),
            memory_pool: MemoryPool::new(),
        })
    }

    /// Returns the latest block height.
    pub fn latest_block_height(&self) -> u32 {
        self.canon_blocks.latest_block_height()
    }

    /// Returns the latest block hash.
    pub fn latest_block_hash(&self) -> N::BlockHash {
        self.canon_blocks.latest_block_hash()
    }

    /// Returns the latest block timestamp.
    pub fn latest_block_timestamp(&self) -> Result<i64> {
        self.canon_blocks.latest_block_timestamp()
    }

    /// Returns the latest block difficulty target.
    pub fn latest_block_difficulty_target(&self) -> Result<u64> {
        self.canon_blocks.latest_block_difficulty_target()
    }

    /// Returns the latest block transactions.
    pub fn latest_block_transactions(&self) -> Result<&Transactions<N>> {
        self.canon_blocks.latest_block_transactions()
    }

    /// Returns the latest block.
    pub fn latest_block(&self) -> Result<Block<N>> {
        self.canon_blocks.latest_block()
    }

    /// Returns `true` if the given block hash exists on the canon chain.
    pub fn contains_block_hash(&self, block_hash: &N::BlockHash) -> bool {
        self.canon_blocks.contains_block_hash(block_hash)
    }

    /// Returns `true` if the given transaction exists on the canon chain.
    pub fn contains_transaction(&self, transaction: &Transaction<N>) -> bool {
        self.canon_blocks.contains_transaction(transaction)
    }

    /// Returns `true` if the given serial numbers root exists.
    pub fn contains_serial_numbers_root(&self, serial_numbers_root: &N::SerialNumbersRoot) -> bool {
        self.canon_blocks.contains_serial_numbers_root(serial_numbers_root)
    }

    /// Returns `true` if the given commitments root exists.
    pub fn contains_commitments_root(&self, commitments_root: &N::CommitmentsRoot) -> bool {
        self.canon_blocks.contains_commitments_root(commitments_root)
    }

    /// Adds the given canon block, if it is well-formed and does not already exist.
    /// Note: This method requires blocks to be added in order of canon block height.
    pub fn add_next_block(&mut self, block: &Block<N>) -> Result<()> {
        // Attempt to insert the block into canon.
        self.canon_blocks.add_next(block)?;

        Ok(())
    }

    /// Adds the given orphan block, if it is well-formed and does not already exist.
    pub fn add_orphan_block(&mut self, block: &Block<N>) -> Result<()> {
        // Ensure the block does not exist in canon.
        if self.canon_blocks.contains_block_hash(&block.to_block_hash()?) {
            return Err(anyhow!("Orphan block already exists in canon chain"));
        }

        // Insert the block into the orphan blocks.
        self.orphan_blocks.insert(block.clone());

        Ok(())
    }

    /// Adds the given unconfirmed transaction to the memory pool.
    pub fn add_unconfirmed_transaction(&mut self, transaction: &Transaction<N>) -> Result<()> {
        // Attempt to add the transaction into the memory pool.
        self.memory_pool.add(transaction)?;

        Ok(())
    }

    /// Mines a new block and adds it to the canon blocks.
    pub fn mine_next_block<R: Rng + CryptoRng>(&mut self, recipient: Address<N>, rng: &mut R) -> Result<()> {
        // Prepare the new block.
        let previous_block_hash = self.latest_block_hash();
        let block_height = self.latest_block_height() + 1;

        // Compute the block difficulty target.
        let previous_timestamp = self.latest_block_timestamp()?;
        let previous_difficulty_target = self.latest_block_difficulty_target()?;
        let block_timestamp = Utc::now().timestamp();
        let difficulty_target = self.canon_blocks.compute_difficulty_target(
            previous_timestamp,
            previous_difficulty_target,
            block_timestamp,
        );

        // Construct the new block transactions.
        let amount = Block::<N>::block_reward(block_height);
        let coinbase_transaction = Transaction::<N>::new_coinbase(recipient, amount, rng)?;
        let transactions = Transactions::from(&[coinbase_transaction])?; // TODO (howardwu): TEMPORARY - Add mempool txs.

        // Construct the new serial numbers root.
        let mut serial_numbers = self.canon_blocks.latest_serial_numbers();
        serial_numbers.add_all(transactions.to_serial_numbers()?)?;
        let serial_numbers_root = serial_numbers.root();

        // Construct the new commitments root.
        let mut commitments = self.canon_blocks.latest_commitments();
        commitments.add_all(transactions.to_commitments()?)?;
        let commitments_root = commitments.root();

        // Mine the next block.
        let block = Block::new(
            previous_block_hash,
            block_height,
            block_timestamp,
            difficulty_target,
            transactions,
            serial_numbers_root,
            commitments_root,
            rng,
        )?;

        // Add the block to canon.
        self.add_next_block(&block)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{testnet1::Testnet1, testnet2::Testnet2};

    #[test]
    fn test_ledger_new() {
        let ledger = Ledger::<Testnet1>::new().unwrap();
        assert_eq!(0, ledger.latest_block_height());

        let ledger = Ledger::<Testnet2>::new().unwrap();
        assert_eq!(0, ledger.latest_block_height());
    }
}
