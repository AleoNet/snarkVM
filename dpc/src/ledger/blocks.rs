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
use snarkvm_algorithms::merkle_tree::*;

use anyhow::{anyhow, Result};
use chrono::Utc;
use itertools::Itertools;
use std::collections::HashMap;

pub const TWO_HOURS_UNIX: i64 = 7200;

#[derive(Clone, Debug)]
pub struct Blocks<N: Network> {
    /// The current block height.
    current_height: u32,
    /// The current block hash.
    current_hash: N::BlockHash,
    /// The current ledger tree.
    ledger_tree: LedgerTree<N>,
    /// The chain of previous block hashes.
    previous_hashes: HashMap<u32, N::BlockHash>,
    /// The chain of block headers.
    headers: HashMap<u32, BlockHeader<N>>,
    /// The chain of block transactions.
    transactions: HashMap<u32, Transactions<N>>,
}

impl<N: Network> Blocks<N> {
    /// Initializes a new instance of `Blocks` with the genesis block.
    pub fn new() -> Result<Self> {
        let genesis_block = N::genesis_block();
        let height = genesis_block.height();

        let mut blocks = Self {
            current_height: height,
            current_hash: genesis_block.hash(),
            ledger_tree: LedgerTree::<N>::new()?,
            previous_hashes: Default::default(),
            headers: Default::default(),
            transactions: Default::default(),
        };

        blocks.ledger_tree.add(&genesis_block.hash())?;
        blocks
            .previous_hashes
            .insert(height, genesis_block.previous_block_hash());
        blocks.headers.insert(height, genesis_block.header().clone());
        blocks.transactions.insert(height, genesis_block.transactions().clone());

        Ok(blocks)
    }

    /// Returns the latest block height.
    pub fn latest_block_height(&self) -> u32 {
        self.current_height
    }

    /// Returns the latest block hash.
    pub fn latest_block_hash(&self) -> N::BlockHash {
        self.current_hash
    }

    /// Returns the latest ledger root.
    pub fn latest_ledger_root(&self) -> N::LedgerRoot {
        self.ledger_tree.root()
    }

    /// Returns the latest block timestamp.
    pub fn latest_block_timestamp(&self) -> Result<i64> {
        Ok(self.get_block_header(self.current_height)?.timestamp())
    }

    /// Returns the latest block difficulty target.
    pub fn latest_block_difficulty_target(&self) -> Result<u64> {
        Ok(self.get_block_header(self.current_height)?.difficulty_target())
    }

    /// Returns the latest cumulative weight.
    pub fn latest_cumulative_weight(&self) -> Result<u128> {
        Ok(self.get_block_header(self.current_height)?.cumulative_weight())
    }

    /// Returns the latest block transactions.
    pub fn latest_block_transactions(&self) -> Result<&Transactions<N>> {
        self.get_block_transactions(self.current_height)
    }

    /// Returns the latest block.
    pub fn latest_block(&self) -> Result<Block<N>> {
        self.get_block(self.current_height)
    }

    /// Returns the previous block hash given the block height.
    pub fn get_previous_block_hash(&self, height: u32) -> Result<N::BlockHash> {
        match self.previous_hashes.get(&height) {
            Some(previous_hash) => Ok(*previous_hash),
            None => Err(anyhow!("Missing previous block hash for height {}", height)),
        }
    }

    /// Returns the block header given the block height.
    pub fn get_block_header(&self, height: u32) -> Result<&BlockHeader<N>> {
        match self.headers.get(&height) {
            Some(header) => Ok(header),
            None => Err(anyhow!("Missing block header for height {}", height)),
        }
    }

    /// Returns the block transactions given the block height.
    pub fn get_block_transactions(&self, height: u32) -> Result<&Transactions<N>> {
        match self.transactions.get(&height) {
            Some(transactions) => Ok(transactions),
            None => Err(anyhow!("Missing block transactions for height {}", height)),
        }
    }

    /// Returns the block given the block height.
    pub fn get_block(&self, height: u32) -> Result<Block<N>> {
        match height == 0 {
            true => Ok(N::genesis_block().clone()),
            false => Ok(Block::from(
                self.get_previous_block_hash(height)?.clone(),
                self.get_block_header(height)?.clone(),
                self.get_block_transactions(height)?.clone(),
            )?),
        }
    }

    /// Returns the block hash given the block height.
    pub fn get_block_hash(&self, height: u32) -> Result<N::BlockHash> {
        if height > self.current_height {
            return Err(anyhow!("Given block height {} is greater than current height", height));
        }

        match height == self.current_height {
            true => Ok(self.current_hash),
            false => match self.previous_hashes.get(&(height + 1)) {
                Some(block_hash) => Ok(*block_hash),
                None => Err(anyhow!("Missing block hash for height {}", height)),
            },
        }
    }

    /// Returns `true` if the given block height exists.
    pub fn contains_height(&self, height: u32) -> bool {
        self.previous_hashes.contains_key(&height)
            || self.headers.contains_key(&height)
            || self.transactions.contains_key(&height)
    }

    /// Returns `true` if the given ledger root exists.
    pub fn contains_ledger_root(&self, ledger_root: &N::LedgerRoot) -> bool {
        *ledger_root == self.latest_ledger_root()
            || self
                .headers
                .values()
                .map(BlockHeader::previous_ledger_root)
                .any(|root| root == *ledger_root)
    }

    /// Returns `true` if the given block hash exists.
    pub fn contains_block_hash(&self, block_hash: &N::BlockHash) -> bool {
        self.current_hash == *block_hash || self.previous_hashes.values().any(|hash| *hash == *block_hash)
    }

    /// Returns `true` if the given transaction exists.
    pub fn contains_transaction(&self, transaction: &Transaction<N>) -> bool {
        self.transactions
            .values()
            .flat_map(|transactions| &**transactions)
            .any(|tx| *tx == *transaction)
    }

    /// Returns `true` if the given serial number exists.
    pub fn contains_serial_number(&self, serial_number: &N::SerialNumber) -> bool {
        self.transactions
            .values()
            .flat_map(|transactions| (**transactions).iter().map(Transaction::serial_numbers))
            .any(|mut serial_numbers| serial_numbers.contains(serial_number))
    }

    /// Returns `true` if the given commitment exists.
    pub fn contains_commitment(&self, commitment: &N::Commitment) -> bool {
        self.transactions
            .values()
            .flat_map(|transactions| (**transactions).iter().map(Transaction::commitments))
            .any(|mut commitments| commitments.contains(commitment))
    }

    /// Adds the given block as the next block in the chain.
    pub fn add_next(&mut self, block: &Block<N>) -> Result<()> {
        // Ensure the block itself is valid.
        if !block.is_valid() {
            return Err(anyhow!("The given block is invalid"));
        }

        // Ensure the next block height is correct.
        let height = block.height();
        if self.current_height + 1 != height {
            return Err(anyhow!("The given block has an incorrect block height"));
        }

        // Ensure the block height does not already exist.
        if self.contains_height(height) {
            return Err(anyhow!("The given block height already exists in the ledger"));
        }

        // Ensure the previous block hash is correct.
        if self.current_hash != block.previous_block_hash() {
            return Err(anyhow!("The given block has an incorrect previous block hash"));
        }

        // Ensure the block hash does not already exist.
        let block_hash = block.hash();
        if self.contains_block_hash(&block_hash) {
            return Err(anyhow!("The given block hash already exists in the ledger"));
        }

        // Ensure the next block timestamp is within the declared time limit.
        let now = Utc::now().timestamp();
        if block.timestamp() > (now + TWO_HOURS_UNIX) {
            return Err(anyhow!("The given block timestamp exceeds the time limit"));
        }

        // Ensure the next block timestamp is after the current block timestamp.
        let current_block = self.latest_block()?;
        if block.timestamp() <= current_block.timestamp() {
            return Err(anyhow!("The given block timestamp is before the current timestamp"));
        }

        // Ensure the expected difficulty target is met.
        let expected_difficulty_target = Blocks::<N>::compute_difficulty_target(
            current_block.timestamp(),
            current_block.difficulty_target(),
            block.timestamp(),
        );
        if block.difficulty_target() != expected_difficulty_target {
            return Err(anyhow!(
                "The given block difficulty target is incorrect. Found {}, but expected {}",
                block.difficulty_target(),
                expected_difficulty_target
            ));
        }

        // Ensure the expected cumulative weight is computed correctly.
        let expected_cumulative_weight = current_block
            .cumulative_weight()
            .saturating_add((u64::MAX / expected_difficulty_target) as u128);
        if block.cumulative_weight() != expected_cumulative_weight {
            return Err(anyhow!(
                "The given cumulative weight is incorrect. Found {}, but expected {}",
                block.cumulative_weight(),
                expected_cumulative_weight
            ));
        }

        for transaction in block.transactions().iter() {
            // Ensure the transaction in the block do not already exist.
            if self.contains_transaction(transaction) {
                return Err(anyhow!("The given block has a duplicate transaction in the ledger"));
            }
            // Ensure the transaction in the block references a valid past or current ledger root.
            if !self.contains_ledger_root(&transaction.ledger_root()) {
                return Err(anyhow!(
                    "The given transaction references a non-existent ledger root {}",
                    &transaction.ledger_root()
                ));
            }
        }

        // Ensure the ledger does not already contain a given serial numbers.
        for serial_number in block.serial_numbers() {
            if self.contains_serial_number(serial_number) {
                return Err(anyhow!("Serial number already exists in the ledger"));
            }
        }

        // Ensure the ledger does not already contain a given commitments.
        for commitment in block.commitments() {
            if self.contains_commitment(commitment) {
                return Err(anyhow!("Commitment already exists in the ledger"));
            }
        }

        // Add the block to the ledger. This code section executes atomically.
        {
            let mut blocks = self.clone();

            blocks.current_height = height;
            blocks.current_hash = block_hash;
            blocks.ledger_tree.add(&block.hash())?;
            blocks.previous_hashes.insert(height, block.previous_block_hash());
            blocks.headers.insert(height, block.header().clone());
            blocks.transactions.insert(height, block.transactions().clone());

            *self = blocks;
        }

        Ok(())
    }

    /// Returns the ledger tree.
    pub fn to_ledger_tree(&self) -> &LedgerTree<N> {
        &self.ledger_tree
    }

    /// Returns an inclusion proof for the ledger tree.
    pub fn to_ledger_root_inclusion_proof(
        &self,
        block_hash: &N::BlockHash,
    ) -> Result<MerklePath<N::LedgerRootParameters>> {
        Ok(self.ledger_tree.to_ledger_inclusion_proof(block_hash)?)
    }

    ///
    /// Returns a ledger proof for the given commitment.
    ///
    pub fn to_ledger_proof(&self, commitment: N::Commitment) -> Result<LedgerProof<N>> {
        // TODO (howardwu): Optimize this operation.
        let transaction = self
            .transactions
            .values()
            .flat_map(|transactions| &**transactions)
            .filter(|transaction| transaction.commitments().contains(&commitment))
            .collect::<Vec<_>>();
        assert_eq!(1, transaction.len()); // TODO (howardwu): Clean this up with a proper error handler.
        let transaction = transaction[0];
        let local_proof = {
            // Initialize a transitions tree.
            let mut transitions_tree = Transitions::<N>::new()?;
            // Add all given transition IDs to the tree.
            transitions_tree.add_all(&transaction.transitions())?;
            // Return the local proof for the transitions tree.
            transitions_tree.to_local_proof(commitment)?
        };
        let transaction_id = local_proof.transaction_id();

        // TODO (howardwu): Optimize this operation.
        let block_height = self
            .transactions
            .iter()
            .filter_map(
                |(block_height, transactions)| match transactions.transaction_ids().contains(&transaction_id) {
                    true => Some(block_height),
                    false => None,
                },
            )
            .collect::<Vec<_>>();
        assert_eq!(1, block_height.len()); // TODO (howardwu): Clean this up with a proper error handler.
        let block_height = *block_height[0];
        let transactions = self.get_block_transactions(block_height)?;
        let block_header = self.get_block_header(block_height)?;

        // Compute the transactions inclusion proof.
        let transactions_inclusion_proof = {
            // TODO (howardwu): Optimize this operation.
            let index = transactions
                .transaction_ids()
                .enumerate()
                .filter_map(|(index, id)| match id == transaction_id {
                    true => Some(index),
                    false => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(1, index.len()); // TODO (howardwu): Clean this up with a proper error handler.
            transactions.to_transactions_inclusion_proof(index[0], transaction_id)?
        };

        // Compute the block header inclusion proof.
        let transactions_root = transactions.transactions_root();
        let block_header_inclusion_proof = block_header.to_header_inclusion_proof(1, transactions_root)?;
        let block_header_root = block_header.to_header_root()?;
        let previous_block_hash = self.get_previous_block_hash(self.current_height)?;
        let current_block_hash = self.current_hash;

        let record_proof = RecordProof::new(
            current_block_hash,
            previous_block_hash,
            block_header_root,
            block_header_inclusion_proof,
            transactions_root,
            transactions_inclusion_proof,
            local_proof,
        )?;

        let ledger_root = self.latest_ledger_root();
        let ledger_root_inclusion_proof = self.to_ledger_root_inclusion_proof(&current_block_hash)?;

        LedgerProof::new(ledger_root, ledger_root_inclusion_proof, record_proof)
    }

    /// Returns the expected difficulty target given the previous block and expected next block details.
    pub fn compute_difficulty_target(previous_timestamp: i64, previous_difficulty_target: u64, timestamp: i64) -> u64 {
        const NUM_BLOCKS_PER_RETARGET: i64 = 1i64;

        /// Bitcoin difficulty retarget algorithm.
        ///     T_{i+1} = T_i * (S / (M * B)).
        ///     M = Number of blocks per retarget.
        ///     B = Expected time per block.
        ///     S = Time elapsed between the last M blocks.
        fn bitcoin_retarget(
            previous_timestamp: i64,
            previous_difficulty: u64,
            block_timestamp: i64,
            target_block_time: i64,
        ) -> u64 {
            let time_elapsed = block_timestamp.saturating_sub(previous_timestamp);
            let time_elapsed = match time_elapsed > 0 {
                true => time_elapsed,
                false => 1,
            };

            let difficulty_factor = time_elapsed as f64 / (NUM_BLOCKS_PER_RETARGET * target_block_time) as f64;

            let new_difficulty = (previous_difficulty as f64) * difficulty_factor;

            match new_difficulty.is_finite() {
                true => new_difficulty as u64,
                false => u64::MAX,
            }
        }

        bitcoin_retarget(
            previous_timestamp,
            previous_difficulty_target,
            timestamp,
            N::ALEO_BLOCK_TIME_IN_SECS,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testnet2::Testnet2;

    use rand::{thread_rng, Rng};

    #[test]
    fn test_retargeting_algorithm_increased() {
        let rng = &mut thread_rng();

        let mut block_difficulty_target = u64::MAX;
        let mut current_timestamp = 0;

        for _ in 0..1000 {
            // Simulate a random block time.
            let simulated_block_time =
                rng.gen_range(Testnet2::ALEO_BLOCK_TIME_IN_SECS / 2..Testnet2::ALEO_BLOCK_TIME_IN_SECS * 2);
            let new_timestamp = current_timestamp + simulated_block_time;

            let new_target = Blocks::<Testnet2>::compute_difficulty_target(
                current_timestamp,
                block_difficulty_target,
                new_timestamp,
            );

            if simulated_block_time < Testnet2::ALEO_BLOCK_TIME_IN_SECS {
                // If the block was found faster than expected, the difficulty should increase.
                assert!(new_target < block_difficulty_target);
            } else if simulated_block_time >= Testnet2::ALEO_BLOCK_TIME_IN_SECS {
                // If the block was found slower than expected, the difficulty should decrease.
                assert!(new_target >= block_difficulty_target);
            }

            current_timestamp = new_timestamp;
            block_difficulty_target = new_target;
        }
    }
}
