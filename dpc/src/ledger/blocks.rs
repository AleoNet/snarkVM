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
use std::collections::HashMap;

pub const TWO_HOURS_UNIX: i64 = 7200;

#[derive(Clone, Debug)]
pub struct Blocks<N: Network> {
    /// The current block height.
    current_height: u32,
    /// The current block hash.
    current_hash: N::BlockHash,
    /// The chain of previous block hashes.
    previous_hashes: HashMap<u32, N::BlockHash>,
    /// The chain of block headers.
    headers: HashMap<u32, BlockHeader<N>>,
    /// The chain of block transactions.
    transactions: HashMap<u32, Transactions<N>>,
    /// The tree of serial numbers.
    serial_numbers: SerialNumbers<N>,
    /// The roots of serial numbers trees.
    serial_numbers_roots: HashMap<u32, N::SerialNumbersRoot>,
    /// The tree of commitments.
    commitments: Commitments<N>,
    /// The roots of commitments trees.
    commitments_roots: HashMap<u32, N::CommitmentsRoot>,
}

impl<N: Network> Blocks<N> {
    /// Initializes a new instance of `Blocks` with the genesis block.
    pub fn new() -> Result<Self> {
        let genesis_block = N::genesis_block().clone();
        let height = genesis_block.height();
        let serial_numbers = genesis_block.to_serial_numbers()?;
        let commitments = genesis_block.to_commitments()?;

        let mut blocks = Self {
            current_height: genesis_block.height(),
            current_hash: genesis_block.to_block_hash()?,
            previous_hashes: Default::default(),
            headers: Default::default(),
            transactions: Default::default(),
            serial_numbers: SerialNumbers::new()?,
            serial_numbers_roots: Default::default(),
            commitments: Commitments::new()?,
            commitments_roots: Default::default(),
        };

        blocks.previous_hashes.insert(height, *genesis_block.previous_hash());
        blocks.headers.insert(height, genesis_block.header().clone());
        blocks.transactions.insert(height, genesis_block.transactions().clone());
        blocks.serial_numbers.add_all(serial_numbers)?;
        blocks.serial_numbers_roots.insert(height, blocks.serial_numbers.root());
        blocks.commitments.add_all(commitments)?;
        blocks.commitments_roots.insert(height, blocks.commitments.root());

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

    /// Returns the latest block timestamp.
    pub fn latest_block_timestamp(&self) -> Result<i64> {
        Ok(self.get_block_header(self.current_height)?.timestamp())
    }

    /// Returns the latest block difficulty target.
    pub fn latest_block_difficulty_target(&self) -> Result<u64> {
        Ok(self.get_block_header(self.current_height)?.difficulty_target())
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

    /// Returns `true` if the given block hash exists.
    pub fn contains_block_hash(&self, block_hash: &N::BlockHash) -> bool {
        self.current_hash == *block_hash || self.previous_hashes.values().filter(|hash| *hash == block_hash).count() > 0
    }

    /// Returns `true` if the given transaction exists.
    pub fn contains_transaction(&self, transaction: &Transaction<N>) -> bool {
        self.transactions
            .values()
            .flat_map(|transactions| &**transactions)
            .filter(|tx| *tx == transaction)
            .count()
            > 0
    }

    /// Returns `true` if the given serial numbers root exists.
    pub fn contains_serial_numbers_root(&self, serial_numbers_root: &N::SerialNumbersRoot) -> bool {
        self.serial_numbers_roots
            .values()
            .filter(|root| *root == serial_numbers_root)
            .count()
            > 0
    }

    /// Returns `true` if the given commitments root exists.
    pub fn contains_commitments_root(&self, commitments_root: &N::CommitmentsRoot) -> bool {
        self.commitments_roots
            .values()
            .filter(|root| *root == commitments_root)
            .count()
            > 0
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
        if self.current_hash != *block.previous_hash() {
            return Err(anyhow!("The given block has an incorrect previous block hash"));
        }

        // Ensure the block hash does not already exist.
        let block_hash = block.to_block_hash()?;
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
        if block.timestamp() < current_block.timestamp() {
            return Err(anyhow!("The given block timestamp is before the current timestamp"));
        }

        // Ensure the expected difficulty target is met.
        let expected_difficulty_target = self.compute_difficulty_target(
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

        // Ensure the transactions in the block do not already exist.
        for transaction in block.transactions().iter() {
            if self.contains_transaction(transaction) {
                return Err(anyhow!("The given block has a duplicate transaction in the ledger"));
            }
        }

        // Ensure the ledger does not already contain a given serial numbers.
        let serial_numbers = block.to_serial_numbers()?;
        for serial_number in &serial_numbers {
            if self.serial_numbers.contains_serial_number(serial_number) {
                return Err(anyhow!("Serial number already exists in the ledger"));
            }
        }

        // Ensure the ledger does not already contain a given commitments.
        let commitments = block.to_commitments()?;
        for commitment in &commitments {
            if self.commitments.contains_commitment(commitment) {
                return Err(anyhow!("Commitment already exists in the ledger"));
            }
        }

        // Add the block to the ledger. This code section executes atomically.
        {
            let mut blocks = self.clone();

            blocks.current_height = height;
            blocks.current_hash = block_hash;
            blocks.previous_hashes.insert(height, *block.previous_hash());
            blocks.headers.insert(height, block.header().clone());
            blocks.transactions.insert(height, block.transactions().clone());
            blocks.serial_numbers.add_all(serial_numbers)?;
            blocks.serial_numbers_roots.insert(height, blocks.serial_numbers.root());
            blocks.commitments.add_all(commitments)?;
            blocks.commitments_roots.insert(height, blocks.commitments.root());

            *self = blocks;
        }

        Ok(())
    }

    /// Returns the expected difficulty target given the previous block and expected next block details.
    fn compute_difficulty_target(
        &self,
        previous_timestamp: i64,
        previous_difficulty_target: u64,
        timestamp: i64,
    ) -> u64 {
        const TARGET_BLOCK_TIME_IN_SECS: i64 = 20i64;

        /// Bitcoin difficulty retarget algorithm.
        fn bitcoin_retarget(
            block_timestamp: i64,
            parent_timestamp: i64,
            target_block_time: i64,
            parent_difficulty: u64,
        ) -> u64 {
            let mut time_elapsed = block_timestamp - parent_timestamp;

            // Limit difficulty adjustment by factor of 2
            if time_elapsed < target_block_time / 2 {
                time_elapsed = target_block_time / 2
            } else if time_elapsed > target_block_time * 2 {
                time_elapsed = target_block_time * 2
            }

            let mut x: u64;
            x = match parent_difficulty.checked_mul(time_elapsed as u64) {
                Some(x) => x,
                None => u64::max_value(),
            };

            x /= target_block_time as u64;
            x
        }

        bitcoin_retarget(
            timestamp,
            previous_timestamp,
            TARGET_BLOCK_TIME_IN_SECS,
            previous_difficulty_target,
        )
    }
}
