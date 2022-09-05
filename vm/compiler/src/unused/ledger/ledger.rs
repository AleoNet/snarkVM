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

use crate::prelude::*;

use anyhow::{anyhow, Result};
use rand::{CryptoRng, Rng};
use std::{collections::HashMap, sync::atomic::AtomicBool};
use time::OffsetDateTime;

#[derive(Clone, Debug)]
pub struct Ledger<N: Network> {
    /// The canonical chain of blocks.
    canon_blocks: Blocks<N>,
    /// The set of unknown orphan blocks.
    orphan_blocks: HashMap<u32, Block<N>>,
    /// The pool of unconfirmed transactions.
    memory_pool: MemoryPool<N>,
}

impl<N: Network> Ledger<N> {
    /// Initializes a new instance of the ledger.
    pub fn new() -> Result<Self> {
        Ok(Self { canon_blocks: Blocks::new()?, orphan_blocks: Default::default(), memory_pool: MemoryPool::new() })
    }

    /// Returns the latest block height.
    pub fn latest_block_height(&self) -> u32 {
        self.canon_blocks.latest_block_height()
    }

    /// Returns the latest block hash.
    pub fn latest_block_hash(&self) -> N::BlockHash {
        self.canon_blocks.latest_block_hash()
    }

    /// Returns the latest ledger root.
    pub fn latest_ledger_root(&self) -> N::LedgerRoot {
        self.canon_blocks.latest_ledger_root()
    }

    /// Returns the latest block timestamp.
    pub fn latest_block_timestamp(&self) -> Result<i64> {
        self.canon_blocks.latest_block_timestamp()
    }

    /// Returns the latest block difficulty target.
    pub fn latest_block_difficulty_target(&self) -> Result<u64> {
        self.canon_blocks.latest_block_difficulty_target()
    }

    /// Returns the latest cumulative weight.
    pub fn latest_cumulative_weight(&self) -> Result<u128> {
        self.canon_blocks.latest_cumulative_weight()
    }

    /// Returns the latest block transactions.
    pub fn latest_block_transactions(&self) -> Result<&Transactions<N>> {
        self.canon_blocks.latest_block_transactions()
    }

    /// Returns the latest block.
    pub fn latest_block(&self) -> Result<Block<N>> {
        self.canon_blocks.latest_block()
    }

    /// Returns `true` if the given ledger root exists on the canon chain.
    pub fn contains_ledger_root(&self, ledger_root: &N::LedgerRoot) -> bool {
        self.canon_blocks.contains_ledger_root(ledger_root)
    }

    /// Returns `true` if the given block hash exists on the canon chain.
    pub fn contains_block_hash(&self, block_hash: &N::BlockHash) -> bool {
        self.canon_blocks.contains_block_hash(block_hash)
    }

    /// Returns `true` if the given transaction exists on the canon chain.
    pub fn contains_transaction(&self, transaction: &Transaction<N>) -> bool {
        self.canon_blocks.contains_transaction(transaction)
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
        if self.canon_blocks.contains_block_hash(&block.hash()) {
            return Err(anyhow!("Orphan block already exists in canon chain"));
        }

        // Insert the block into the orphan blocks.
        self.orphan_blocks.insert(block.height(), block.clone());

        Ok(())
    }

    /// Adds the given unconfirmed transaction to the memory pool.
    pub fn add_unconfirmed_transaction(&mut self, transaction: &Transaction<N>) -> Result<()> {
        // Ensure the transaction contains ledger roots from the canon chain.
        if !self.canon_blocks.contains_ledger_root(&transaction.ledger_root()) {
            return Err(anyhow!("Transaction references a non-existent ledger root"));
        }

        // Ensure the transaction does not contain serial numbers already in the canon chain.
        for serial_number in transaction.serial_numbers() {
            if self.canon_blocks.contains_serial_number(serial_number) {
                return Err(anyhow!("Transaction contains a serial number already in existence"));
            }
        }

        // Ensure the transaction does not contain commitments already in the canon chain.
        for commitment in transaction.commitments() {
            if self.canon_blocks.contains_commitment(commitment) {
                return Err(anyhow!("Transaction contains a commitment already in existence"));
            }
        }

        // Attempt to add the transaction into the memory pool.
        self.memory_pool.add_transaction(transaction)?;

        Ok(())
    }

    /// Mines a new block and adds it to the canon blocks.
    pub fn mine_next_block<R: Rng + CryptoRng>(
        &mut self,
        recipient: Address<N>,
        is_public: bool,
        terminator: &AtomicBool,
        rng: &mut R,
    ) -> Result<Record<N>> {
        // Prepare the new block.
        let previous_block_hash = self.latest_block_hash();
        let block_height = self.latest_block_height() + 1;

        // Ensure that the new timestamp is ahead of the previous timestamp.
        let block_timestamp =
            std::cmp::max(OffsetDateTime::now_utc().unix_timestamp(), self.latest_block_timestamp()?.saturating_add(1));

        // Compute the block difficulty target.
        let difficulty_target =
            Blocks::<N>::compute_difficulty_target(N::genesis_block().header(), block_timestamp, block_height);

        // Compute the cumulative weight.
        let cumulative_weight = self.latest_cumulative_weight()?.saturating_add((u64::MAX / difficulty_target) as u128);

        // Construct the new block transactions.
        let amount = Block::<N>::block_reward(block_height);
        let (coinbase_transaction, coinbase_record) =
            Transaction::<N>::new_coinbase(recipient, amount, is_public, rng)?;
        let transactions = Transactions::from(&[vec![coinbase_transaction], self.memory_pool.transactions()].concat())?;

        // Retrieve the current ledger root.
        let previous_ledger_root = self.canon_blocks.latest_ledger_root();

        // Construct the block template.
        let template = BlockTemplate::new(
            previous_block_hash,
            block_height,
            block_timestamp,
            difficulty_target,
            cumulative_weight,
            previous_ledger_root,
            transactions,
            coinbase_record.clone(),
        );

        // Mine the next block.
        let block = Block::mine(&template, terminator, rng)?;

        // Attempt to add the block to the canon chain.
        self.add_next_block(&block)?;

        // On success, clear the memory pool of its transactions.
        self.memory_pool.clear_all_transactions();

        Ok(coinbase_record)
    }

    /// Returns the ledger tree.
    pub fn to_ledger_tree(&self) -> &LedgerTree<N> {
        self.canon_blocks.to_ledger_tree()
    }

    ///
    /// Returns the ledger proof for the given commitment with the current ledger root.
    ///
    pub fn to_ledger_proof(&self, commitment: N::Commitment) -> Result<LedgerProof<N>> {
        self.canon_blocks.to_ledger_proof(commitment)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{testnet1::Testnet1, testnet2::Testnet2};

    use rand::thread_rng;

    #[test]
    fn test_new() {
        let ledger = Ledger::<Testnet1>::new().unwrap();
        assert_eq!(0, ledger.latest_block_height());

        let ledger = Ledger::<Testnet2>::new().unwrap();
        assert_eq!(0, ledger.latest_block_height());
    }

    #[test]
    fn test_mine_next_block() {
        let rng = &mut thread_rng();
        {
            let mut ledger = Ledger::<Testnet1>::new().unwrap();
            let recipient = Account::<Testnet1>::new(rng);

            assert_eq!(0, ledger.latest_block_height());
            ledger.mine_next_block(recipient.address(), true, &AtomicBool::new(false), rng).unwrap();
            assert_eq!(1, ledger.latest_block_height());
        }
        {
            let mut ledger = Ledger::<Testnet2>::new().unwrap();
            let recipient = Account::<Testnet2>::new(rng);

            assert_eq!(0, ledger.latest_block_height());
            ledger.mine_next_block(recipient.address(), true, &AtomicBool::new(false), rng).unwrap();
            assert_eq!(1, ledger.latest_block_height());
        }
    }
}
