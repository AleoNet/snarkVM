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

use crate::ledger::{Header, Transactions};

use anyhow::{anyhow, Result};
use itertools::Itertools;
use std::collections::HashMap;
use time::OffsetDateTime;

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
    headers: HashMap<u32, Header<N>>,
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
        blocks.previous_hashes.insert(height, genesis_block.previous_block_hash());
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
    pub fn get_block_header(&self, height: u32) -> Result<&Header<N>> {
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
                self.get_previous_block_hash(height)?,
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
            || self.headers.values().map(Header::previous_ledger_root).any(|root| root == *ledger_root)
    }

    /// Returns `true` if the given block hash exists.
    pub fn contains_block_hash(&self, block_hash: &N::BlockHash) -> bool {
        self.current_hash == *block_hash || self.previous_hashes.values().any(|hash| *hash == *block_hash)
    }

    /// Returns `true` if the given transaction exists.
    pub fn contains_transaction(&self, transaction: &Transaction<N>) -> bool {
        self.transactions.values().flat_map(|transactions| &**transactions).any(|tx| *tx == *transaction)
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
        let now = OffsetDateTime::now_utc().unix_timestamp();
        if block.timestamp() > (now + N::ALEO_FUTURE_TIME_LIMIT_IN_SECS) {
            return Err(anyhow!("The given block timestamp exceeds the time limit"));
        }

        // Ensure the next block timestamp is after the current block timestamp.
        let current_block = self.latest_block()?;
        if block.timestamp() <= current_block.timestamp() {
            return Err(anyhow!("The given block timestamp is before the current timestamp"));
        }

        // Ensure the expected difficulty target is met.
        let expected_difficulty_target =
            Blocks::<N>::compute_difficulty_target(N::genesis_block().header(), block.timestamp(), block.height());
        if block.difficulty_target() != expected_difficulty_target {
            return Err(anyhow!(
                "The given block difficulty target is incorrect. Found {}, but expected {}",
                block.difficulty_target(),
                expected_difficulty_target
            ));
        }

        // Ensure the expected cumulative weight is computed correctly.
        let expected_cumulative_weight =
            current_block.cumulative_weight().saturating_add((u64::MAX / expected_difficulty_target) as u128);
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
        self.ledger_tree.to_ledger_inclusion_proof(block_hash)
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

        if transaction.len() != 1 {
            return Err(anyhow!("Multiple transactions associated with commitment {}", commitment.to_string()));
        }

        let transaction = transaction[0];
        let local_proof = {
            // Initialize a transitions tree.
            let mut transitions_tree = Transitions::<N>::new()?;
            // Add all given transition IDs to the tree.
            transitions_tree.add_all(transaction.transitions())?;
            // Return the local proof for the transitions tree.
            transitions_tree.to_local_proof(commitment)?
        };
        let transaction_id = local_proof.transaction_id();

        // TODO (howardwu): Optimize this operation.
        let block_height = self
            .transactions
            .iter()
            .filter_map(|(block_height, transactions)| match transactions.transaction_ids().contains(&transaction_id) {
                true => Some(block_height),
                false => None,
            })
            .collect::<Vec<_>>();

        if block_height.len() != 1 {
            return Err(anyhow!("Multiple blocks associated with transaction {}", transaction_id.to_string()));
        }

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

            if index.len() != 1 {
                return Err(anyhow!("Block contains multiple transactions with the id {}", transaction_id.to_string()));
            }

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
    pub fn compute_difficulty_target(
        anchor_block_header: &Header<N>,
        block_timestamp: i64,
        block_height: u32,
    ) -> u64 {
        Self::asert_retarget(
            anchor_block_header.timestamp(),
            anchor_block_header.difficulty_target(),
            anchor_block_header.height(),
            block_timestamp,
            block_height,
            N::ALEO_BLOCK_TIME_IN_SECS,
        )
    }

    /// ASERT difficulty retarget algorithm based on https://www.reference.cash/protocol/forks/2020-11-15-asert.
    ///     T_{i+1} = T_anchor * 2^((S - B * N) / tau).
    ///     T_anchor = Anchor target of a specific block height
    ///     B = Expected time per block.
    ///     S = Time elapsed since the anchor.
    ///     N = Number of blocks since the anchor.
    ///     tau = The half life of the algorithm. For every `tau` seconds ahead of
    ///           schedule a block’s timestamp becomes, the difficulty doubles.
    /// To avoid use of floating points, we use fixed-point arithmetic.
    fn asert_retarget(
        anchor_timestamp: i64,
        anchor_difficulty_target: u64,
        anchor_block_height: u32,
        block_timestamp: i64,
        block_height: u32,
        target_block_time: i64,
    ) -> u64 {
        // Compute the difference in block time elapsed, defined as:
        // (block_timestamp - anchor_timestamp) - target_block_time * number_of_blocks_elapsed.
        let drift = {
            // Determine the block time elapsed (in seconds) since the anchor block.
            // Note: This operation includes a safety check for a repeat timestamp.
            let block_time_elapsed = core::cmp::max(block_timestamp.saturating_sub(anchor_timestamp), 1);

            // Determine the number of blocks since the anchor.
            // Note: This operation includes a safety check for a repeat block height.
            let number_of_blocks_elapsed = core::cmp::max(block_height.saturating_sub(anchor_block_height), 1);

            // Determine the expected block time elapsed (in seconds) since the anchor block.
            let expected_block_time_elapsed = target_block_time.saturating_mul(number_of_blocks_elapsed as i64);

            // Determine the difference in block time elapsed (in seconds).
            // Note: This operation must be *standard subtraction* to account for faster blocks.
            block_time_elapsed - expected_block_time_elapsed
        };

        // Constants used for fixed point arithmetic.
        const RBITS: u32 = 16;
        const RADIX: u128 = 1 << RBITS;

        // The half life for the expected duration in doubling the difficulty target.
        const TAU: u128 = 64_800; // 64,800 seconds = 18 hours

        // Compute the exponent factor, and decompose it into integral & fractional parts for fixed point arithmetic.
        let (integral, fractional) = {
            // Calculate the exponent factor.
            let exponent = (RADIX as i128).saturating_mul(drift as i128) / (TAU as i128);

            // Decompose into the integral and fractional parts.
            let integral = exponent >> RBITS;
            let fractional = (exponent - (integral << RBITS)) as u128;
            assert!(fractional < RADIX, "Ensure fractional part is within fixed point size");
            assert_eq!(exponent, integral * (RADIX as i128) + fractional as i128);

            (integral, fractional)
        };

        // Approximate the fractional multiplier as 2^RBITS * 2^fractional, where:
        // 2^x ~= (1 + 0.695502049*x + 0.2262698*x**2 + 0.0782318*x**3)
        let fractional_multiplier = RADIX
            + ((195_766_423_245_049_u128 * fractional
            + 971_821_376_u128 * fractional.pow(2)
            + 5_127_u128 * fractional.pow(3)
            + 2_u128.pow(RBITS * 3 - 1))
            >> (RBITS * 3));

        // Cast the anchor difficulty target from a u64 to a u128.
        // The difficulty target must allow for leading zeros to account for overflows;
        // an additional 64-bits for the leading zeros suffices.
        let candidate_difficulty_target = (anchor_difficulty_target as u128).saturating_mul(fractional_multiplier);

        // Calculate the new difficulty.
        // Shift the target to multiply by 2^(integer) / RADIX.
        let shifts = integral - RBITS as i128;
        let mut candidate_difficulty_target = if shifts < 0 {
            match candidate_difficulty_target.checked_shr((-shifts) as u32) {
                Some(target) => core::cmp::max(target, 1),
                None => 1,
            }
        } else {
            match candidate_difficulty_target.checked_shl(shifts as u32) {
                Some(target) => core::cmp::max(target, 1),
                None => u64::MAX as u128,
            }
        };

        // Cap the difficulty target at `u64::MAX` if it has overflowed.
        candidate_difficulty_target = core::cmp::min(candidate_difficulty_target, u64::MAX as u128);

        // Cast the new difficulty target down from a u128 to a u64.
        // Ensure that the leading 64 bits are zeros.
        assert_eq!(candidate_difficulty_target.checked_shr(64), Some(0));
        candidate_difficulty_target as u64
    }
}

#[cfg(test)]
#[allow(clippy::comparison_chain)]
mod tests {
    use super::*;
    use crate::console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_asert_difficulty_target_simple() {
        let anchor_timestamp = 1640179531i64;
        let anchor_block_height = 72154u32;
        let anchor_difficulty_target = 101336179232188u64;

        //
        // Simulate block times from T-19 to T+19 seconds,
        // where T := anchor_timestamp + ALEO_BLOCK_TIME_IN_SECS.
        //
        for i in -19..20 {
            // Simulate a random block time.
            let simulated_block_time = CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS + i;
            let simulated_block_height = anchor_block_height + 1;

            let expected_time_elapsed =
                (simulated_block_height - anchor_block_height) as i64 * CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS;
            let simulated_time_elapsed = (simulated_block_height - anchor_block_height) as i64 * simulated_block_time;

            let simulated_timestamp = anchor_timestamp.saturating_add(simulated_time_elapsed);
            let candidate_difficulty_target = Blocks::<CurrentNetwork>::asert_retarget(
                anchor_timestamp,
                anchor_difficulty_target,
                anchor_block_height,
                simulated_timestamp,
                simulated_block_height,
                CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS,
            );

            println!(
                "Anchor (height = {:?}, timestamp = {:?}, difficulty_target = {:?})",
                anchor_block_height, anchor_timestamp, anchor_difficulty_target
            );
            println!(
                "Block (height = {:?}, timestamp = {:?}, difficulty_target = {:?})",
                simulated_block_height, simulated_timestamp, candidate_difficulty_target
            );
            println!(
                "Difference (height = {:?}, drift = {:?}, delta_in_difficulty_target = {:?})",
                simulated_block_height - anchor_block_height,
                simulated_time_elapsed - expected_time_elapsed,
                candidate_difficulty_target.wrapping_sub(anchor_difficulty_target),
            );

            if simulated_block_time < CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS {
                println!("{} < {}\n", simulated_block_time, CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS);
                // If the block was found faster than expected, the difficulty should increase.
                assert!(candidate_difficulty_target < anchor_difficulty_target);
            } else if simulated_block_time == CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS {
                println!("{} == {}\n", simulated_block_time, CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS);
                // If the block was found within the expected time, the difficulty should stay unchanged.
                assert_eq!(candidate_difficulty_target, anchor_difficulty_target);
            } else if simulated_block_time > CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS {
                println!("{} > {}\n", simulated_block_time, CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS);
                // If the block was found slower than expected, the difficulty should decrease.
                assert!(candidate_difficulty_target > anchor_difficulty_target);
            }
        }
    }

    #[test]
    fn test_asert_difficulty_target_anchored() {
        let anchor_timestamp = 1640179531i64;
        let anchor_block_height = 72154u32;
        let anchor_difficulty_target = 101336179232188u64;

        const TAU: u128 = 64_800; // 64,800 seconds = 18 hours

        for num_blocks_since_anchor in 1..500_000 {
            //
            // Simulate block times from T-5 to T+5 seconds,
            // where T := anchor_timestamp + ALEO_BLOCK_TIME_IN_SECS.
            //
            for j in -5..5 {
                // Simulate a random block time.
                let simulated_block_time = CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS + j;
                let simulated_block_height = anchor_block_height + num_blocks_since_anchor;

                let expected_time_elapsed =
                    (simulated_block_height - anchor_block_height) as i64 * CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS;
                let simulated_time_elapsed =
                    (simulated_block_height - anchor_block_height) as i64 * simulated_block_time;
                let drift = simulated_time_elapsed - expected_time_elapsed;

                let simulated_timestamp = anchor_timestamp.saturating_add(simulated_time_elapsed);
                let candidate_difficulty_target = Blocks::<CurrentNetwork>::asert_retarget(
                    anchor_timestamp,
                    anchor_difficulty_target,
                    anchor_block_height,
                    simulated_timestamp,
                    simulated_block_height,
                    CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS,
                );

                // Calculate the number of times the drift has doubled from TAU.
                let drift_multiplier = drift as f64 / TAU as f64;
                let difficulty_ratio = candidate_difficulty_target as f64 / anchor_difficulty_target as f64;

                println!(
                    "Anchor (height = {:?}, timestamp = {:?}, difficulty_target = {:?})",
                    anchor_block_height, anchor_timestamp, anchor_difficulty_target
                );
                println!(
                    "Block (height = {:?}, timestamp = {:?}, difficulty_target = {:?})",
                    simulated_block_height, simulated_timestamp, candidate_difficulty_target
                );
                println!(
                    "Difference (height = {}, drift = {}, difficulty_ratio = {}, drift_multiplier = {})",
                    simulated_block_height - anchor_block_height,
                    drift,
                    difficulty_ratio,
                    drift_multiplier
                );

                // Ensure the difficulty is doubling when the drift doubles,
                // and halving when the drift is half the expected time elapsed.
                let expected_difficulty_ratio = 2f64.powf(drift_multiplier);
                // Only check the difficulty targets that naturally fall below u64::MAX,
                // which is determined by approximating (flooring) the expected difficulty ratio
                // and seeing if the new difficulty target overflows or not.
                if anchor_difficulty_target.checked_mul(expected_difficulty_ratio as u64).is_some() {
                    let percentage_difference =
                        100f64 * (expected_difficulty_ratio - difficulty_ratio).abs() / difficulty_ratio;
                    assert!(percentage_difference < 1f64);
                }

                if simulated_block_time < CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS {
                    println!("{} < {}\n", simulated_block_time, CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS);
                    // If the block was found faster than expected, the difficulty should increase.
                    assert!(candidate_difficulty_target < anchor_difficulty_target);
                } else if simulated_block_time == CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS {
                    println!("{} == {}\n", simulated_block_time, CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS);
                    // If the block was found within the expected time, the difficulty should stay unchanged.
                    assert_eq!(candidate_difficulty_target, anchor_difficulty_target);
                } else if simulated_block_time > CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS {
                    println!("{} > {}\n", simulated_block_time, CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS);
                    // If the block was found slower than expected, the difficulty should decrease.
                    assert!(candidate_difficulty_target > anchor_difficulty_target);
                }
            }
        }
    }

    #[test]
    fn test_asert_difficulty_target_random() {
        let rng = &mut thread_rng();

        for _ in 0..1_000_000 {
            let anchor_timestamp = rng.gen_range(0..1_000_000_000_i64);
            let anchor_block_height = rng.gen_range(0..u32::MAX);
            let anchor_difficulty_target = rng.gen_range(1..u64::MAX);

            // Simulate a random block time.
            let simulated_block_time = rng.gen_range(1..CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS + 100);
            let simulated_block_height = anchor_block_height.saturating_add(rng.gen_range(1..10_000_u32));

            let expected_time_elapsed =
                (simulated_block_height - anchor_block_height) as i64 * CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS;
            let simulated_time_elapsed = (simulated_block_height - anchor_block_height) as i64 * simulated_block_time;

            let simulated_timestamp = anchor_timestamp.saturating_add(simulated_time_elapsed);
            let candidate_difficulty_target = Blocks::<CurrentNetwork>::asert_retarget(
                anchor_timestamp,
                anchor_difficulty_target,
                anchor_block_height,
                simulated_timestamp,
                simulated_block_height,
                CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS,
            );

            println!(
                "Anchor (height = {:?}, timestamp = {:?}, difficulty_target = {:?})",
                anchor_block_height, anchor_timestamp, anchor_difficulty_target
            );
            println!(
                "Block (height = {:?}, timestamp = {:?}, difficulty_target = {:?})",
                simulated_block_height, simulated_timestamp, candidate_difficulty_target
            );
            println!(
                "Difference (height = {:?}, drift = {:?}, delta_in_difficulty_target = {:?})",
                simulated_block_height - anchor_block_height,
                simulated_time_elapsed - expected_time_elapsed,
                candidate_difficulty_target.wrapping_sub(anchor_difficulty_target),
            );

            if simulated_block_time < CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS {
                println!("{} < {}\n", simulated_block_time, CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS);
                // If the block was found faster than expected, the difficulty should increase.
                assert!(candidate_difficulty_target < anchor_difficulty_target);
            } else if simulated_block_time == CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS {
                println!("{} == {}\n", simulated_block_time, CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS);
                // If the block was found within the expected time, the difficulty should stay unchanged.
                assert_eq!(candidate_difficulty_target, anchor_difficulty_target);
            } else if simulated_block_time > CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS {
                println!("{} > {}\n", simulated_block_time, CurrentNetwork::ALEO_BLOCK_TIME_IN_SECS);
                // If the block was found slower than expected, the difficulty should decrease.
                assert!(candidate_difficulty_target > anchor_difficulty_target);
            }
        }
    }
}
