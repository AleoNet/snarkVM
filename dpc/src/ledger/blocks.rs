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
            current_hash: genesis_block.block_hash(),
            previous_hashes: Default::default(),
            headers: Default::default(),
            transactions: Default::default(),
        };

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

    /// Returns `true` if the given ledger root exists.
    pub fn contains_ledger_root(&self, ledger_root: &N::LedgerRoot) -> bool {
        self.headers
            .values()
            .map(BlockHeader::ledger_root)
            .filter(|root| root == ledger_root)
            .count()
            > 0
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

    /// Returns `true` if the given serial number exists.
    pub fn contains_serial_number(&self, serial_number: &N::SerialNumber) -> bool {
        // TODO (howardwu): Optimize this operation.
        self.transactions
            .values()
            .flat_map(|transactions| (**transactions).iter().map(Transaction::serial_numbers))
            .filter(|serial_numbers| serial_numbers.contains(serial_number))
            .count()
            > 0
    }

    /// Returns `true` if the given commitment exists.
    pub fn contains_commitment(&self, commitment: &N::Commitment) -> bool {
        // TODO (howardwu): Optimize this operation.
        self.transactions
            .values()
            .flat_map(|transactions| (**transactions).iter().map(Transaction::commitments))
            .filter(|commitments| commitments.contains(commitment))
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
        if self.current_hash != block.previous_block_hash() {
            return Err(anyhow!("The given block has an incorrect previous block hash"));
        }

        // Ensure the block hash does not already exist.
        let block_hash = block.block_hash();
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

        for transaction in block.transactions().iter() {
            // Ensure the transaction in the block do not already exist.
            if self.contains_transaction(transaction) {
                return Err(anyhow!("The given block has a duplicate transaction in the ledger"));
            }
            // Ensure the transaction in the block references a valid past or current ledger root.
            for ledger_root in &transaction.ledger_roots() {
                if !self.contains_ledger_root(ledger_root) {
                    return Err(anyhow!(
                        "The given transaction references a non-existent ledger root {}",
                        ledger_root
                    ));
                }
            }
        }

        // Ensure the ledger does not already contain a given serial numbers.
        let serial_numbers = block.serial_numbers();
        for serial_number in &serial_numbers {
            if self.contains_serial_number(serial_number) {
                return Err(anyhow!("Serial number already exists in the ledger"));
            }
        }

        // Ensure the ledger does not already contain a given commitments.
        let commitments = block.commitments();
        for commitment in &commitments {
            if self.contains_commitment(commitment) {
                return Err(anyhow!("Commitment already exists in the ledger"));
            }
        }

        // Add the block to the ledger. This code section executes atomically.
        {
            let mut blocks = self.clone();

            blocks.current_height = height;
            blocks.current_hash = block_hash;
            blocks.previous_hashes.insert(height, block.previous_block_hash());
            blocks.headers.insert(height, block.header().clone());
            blocks.transactions.insert(height, block.transactions().clone());

            *self = blocks;
        }

        Ok(())
    }

    // TODO (howardwu): Optimize this function.
    pub fn to_ledger_root(&self) -> Result<N::LedgerRoot> {
        let mut ledger = LedgerTree::<N>::new()?;
        ledger.add_all(
            self.previous_hashes
                .values()
                .chain(vec![self.current_hash].iter())
                .cloned()
                .collect::<Vec<_>>()
                .as_slice(),
        )?;
        Ok(ledger.root())
    }

    // TODO (howardwu): Optimize this function.
    /// Returns an inclusion proof for the ledger tree.
    pub fn to_ledger_root_inclusion_proof(
        &self,
        block_hash: &N::BlockHash,
    ) -> Result<MerklePath<N::LedgerRootParameters>> {
        let mut ledger = LedgerTree::<N>::new()?;
        ledger.add_all(
            self.previous_hashes
                .values()
                .chain(vec![self.current_hash].iter())
                .cloned()
                .collect::<Vec<_>>()
                .as_slice(),
        )?;
        Ok(ledger.to_ledger_inclusion_proof(block_hash)?)
    }

    ///
    /// Returns a ledger proof for the given commitment.
    ///
    pub fn to_ledger_inclusion_proof(&self, commitment: N::Commitment) -> Result<LedgerProof<N>> {
        // TODO (howardwu): Optimize this operation.
        let transaction = self
            .transactions
            .values()
            .flat_map(|transactions| &**transactions)
            .filter(|transaction| transaction.commitments().contains(&commitment))
            .collect::<Vec<_>>();
        assert_eq!(1, transaction.len()); // TODO (howardwu): Clean this up with a proper error handler.
        let transaction = transaction[0];
        let transaction_id = transaction.transaction_id();

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

        // TODO (howardwu): Optimize this operation.
        let transition = transaction
            .transitions()
            .iter()
            .filter(|transition| transition.commitments().contains(&commitment))
            .collect::<Vec<_>>();
        assert_eq!(1, transition.len()); // TODO (howardwu): Clean this up with a proper error handler.
        let transition = transition[0].clone();
        let transition_id = transition.transition_id();

        // Compute the transition inclusion proof.
        let transition_inclusion_proof = {
            // TODO (howardwu): Optimize this operation.
            // It is either leaf 4 or 5.
            if let Ok(proof) = transition.to_transition_inclusion_proof(4, commitment) {
                proof
            } else if let Ok(proof) = transition.to_transition_inclusion_proof(5, commitment) {
                proof
            } else {
                unreachable!() // TODO (howardwu): Clean this up with a proper error handler.
            }
        };

        // Compute the transaction inclusion proof.
        let transaction_inclusion_proof = transaction.to_transaction_inclusion_proof(transition_id)?;

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
        let transactions_root = transactions.to_transactions_root()?;
        let block_header_inclusion_proof = block_header.to_header_inclusion_proof(1, transactions_root)?;
        let block_header_root = block_header.to_header_root()?;
        let previous_block_hash = self.get_previous_block_hash(self.current_height)?;
        let current_block_hash = self.current_hash;

        // TODO (howardwu): Optimize this operation.
        let ledger_root = self.to_ledger_root()?;
        let ledger_root_inclusion_proof = self.to_ledger_root_inclusion_proof(&current_block_hash)?;

        LedgerProof::new(
            ledger_root,
            ledger_root_inclusion_proof,
            current_block_hash,
            previous_block_hash,
            block_header_root,
            block_header_inclusion_proof,
            transactions_root,
            transactions_inclusion_proof,
            transaction_id,
            transaction_inclusion_proof,
            transition_id,
            transition_inclusion_proof,
            commitment,
        )
    }

    /// Returns the expected difficulty target given the previous block and expected next block details.
    pub fn compute_difficulty_target(previous_timestamp: i64, previous_difficulty_target: u64, timestamp: i64) -> u64 {
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
