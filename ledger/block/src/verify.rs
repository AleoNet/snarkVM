// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]

use super::*;
use ledger_coinbase::{CoinbasePuzzle, EpochChallenge};
use synthesizer_program::FinalizeOperation;

use std::collections::HashSet;

#[cfg(not(feature = "serial"))]
use rayon::prelude::*;

impl<N: Network> Block<N> {
    /// Ensures the block is correct.
    pub fn verify(
        &self,
        previous_block: &Block<N>,
        current_state_root: N::StateRoot,
        current_committee: &Committee<N>,
        current_puzzle: &CoinbasePuzzle<N>,
        current_epoch_challenge: &EpochChallenge<N>,
        current_timestamp: i64,
        ratified_finalize_operations: Vec<FinalizeOperation<N>>,
    ) -> Result<()> {
        // Ensure the block hash is correct.
        self.verify_hash(previous_block.height(), previous_block.hash())?;

        // Ensure the block authority is correct.
        let (expected_round, expected_height, expected_timestamp) =
            self.verify_authority(previous_block.round(), previous_block.height(), current_committee)?;

        // Ensure the block solutions are correct.
        let (
            expected_cumulative_weight,
            expected_cumulative_proof_target,
            expected_coinbase_target,
            expected_proof_target,
            expected_last_coinbase_target,
            expected_last_coinbase_timestamp,
            mut expected_block_reward,
            expected_puzzle_reward,
        ) = self.verify_solutions(previous_block, current_puzzle, current_epoch_challenge)?;

        // Add the priority fees to the block reward.
        for confirmed_transacation in self.transactions.iter() {
            // Get the priority fee amount for the transaction.
            let priority_fee_amount = confirmed_transacation.transaction().priority_fee_amount()?;

            // Add the priority fee to the block reward.
            expected_block_reward = expected_block_reward.saturating_add(*priority_fee_amount);
        }

        // Ensure the block ratifications are correct.
        self.verify_ratifications(expected_block_reward, expected_puzzle_reward)?;

        // Ensure the block transactions are correct.
        self.verify_transactions()?;

        // Set the expected previous state root.
        let expected_previous_state_root = current_state_root;
        // Compute the expected transactions root.
        let expected_transactions_root = self.compute_transactions_root()?;
        // Compute the expected finalize root.
        let expected_finalize_root = self.compute_finalize_root(ratified_finalize_operations)?;
        // Compute the expected ratifications root.
        let expected_ratifications_root = self.compute_ratifications_root()?;
        // Compute the expected solutions root.
        let expected_solutions_root = self.compute_solutions_root()?;
        // Compute the expected subdag root.
        let expected_subdag_root = self.compute_subdag_root()?;

        // Ensure the block header is correct.
        self.header.verify(
            expected_previous_state_root,
            expected_transactions_root,
            expected_finalize_root,
            expected_ratifications_root,
            expected_solutions_root,
            expected_subdag_root,
            expected_round,
            expected_height,
            expected_cumulative_weight,
            expected_cumulative_proof_target,
            expected_coinbase_target,
            expected_proof_target,
            expected_last_coinbase_target,
            expected_last_coinbase_timestamp,
            expected_timestamp,
            current_timestamp,
        )
    }
}

impl<N: Network> Block<N> {
    /// Ensures the block hash is correct.
    fn verify_hash(&self, previous_height: u32, previous_hash: N::BlockHash) -> Result<(), Error> {
        // Determine the expected height.
        let expected_height = previous_height.saturating_add(1);

        // Ensure the previous block hash matches.
        ensure!(
            self.previous_hash == previous_hash,
            "Previous block hash is incorrect in block {expected_height} (found '{}', expected '{}')",
            self.previous_hash,
            previous_hash
        );

        // Compute the Merkle root of the block header.
        let Ok(header_root) = self.header.to_root() else {
            bail!("Failed to compute the Merkle root of the block header");
        };
        // Compute the block hash.
        let candidate_hash = match N::hash_bhp1024(&to_bits_le![previous_hash, header_root]) {
            Ok(candidate_hash) => candidate_hash,
            Err(error) => bail!("Failed to compute the block hash for block {expected_height} - {error}"),
        };
        // Ensure the block hash matches.
        ensure!(
            *self.block_hash == candidate_hash,
            "Block hash is incorrect in block {expected_height} (found '{}', expected '{}')",
            self.block_hash,
            Into::<N::BlockHash>::into(candidate_hash)
        );
        // Return success.
        Ok(())
    }

    /// Ensures the block authority is correct.
    fn verify_authority(
        &self,
        previous_round: u64,
        previous_height: u32,
        current_committee: &Committee<N>,
    ) -> Result<(u64, u32, i64)> {
        // Determine the expected height.
        let expected_height = previous_height.saturating_add(1);
        // Ensure the block type is correct.
        match expected_height == 0 {
            true => ensure!(self.authority.is_beacon(), "The genesis block must be a beacon block"),
            false => {
                #[cfg(not(any(test, feature = "test")))]
                ensure!(self.authority.is_quorum(), "The next block must be a quorum block");
            }
        }

        // Determine the expected round.
        let expected_round = match &self.authority {
            // Beacon blocks increment the previous block round by 1.
            Authority::Beacon(..) => previous_round.saturating_add(1),
            // Quorum blocks use the subdag anchor round.
            Authority::Quorum(subdag) => {
                // Ensure the subdag anchor round is after the previous block round.
                ensure!(
                    subdag.anchor_round() > previous_round,
                    "Subdag anchor round is not after previous block round in block {} (found '{}', expected after '{}')",
                    expected_height,
                    subdag.anchor_round(),
                    previous_round
                );
                // Output the subdag anchor round.
                subdag.anchor_round()
            }
        };
        // Ensure the block round is at least the starting round of the committee.
        ensure!(
            expected_round >= current_committee.starting_round(),
            "Block {} has an invalid round (found '{expected_round}', expected at least '{}')",
            expected_height,
            current_committee.starting_round()
        );

        // Ensure the block authority is correct.
        match &self.authority {
            Authority::Beacon(signature) => {
                // Retrieve the signer.
                let signer = signature.to_address();
                // Ensure the block is signed by a committee member.
                ensure!(
                    current_committee.members().contains_key(&signer),
                    "Beacon block {expected_height} has a signer not in the committee (found '{signer}')",
                );
                // Ensure the signature is valid.
                ensure!(
                    signature.verify(&signer, &[*self.block_hash]),
                    "Signature is invalid in block {expected_height}"
                );
            }
            Authority::Quorum(subdag) => {
                // Compute the expected leader.
                let expected_leader = current_committee.get_leader(expected_round)?;
                // Ensure the block is authored by the expected leader.
                ensure!(
                    subdag.leader_address() == expected_leader,
                    "Quorum block {expected_height} is authored by an unexpected leader (found: {}, expected: {expected_leader})",
                    subdag.leader_address()
                );
                // Ensure the transmission IDs from the subdag correspond to the block.
                Self::check_subdag_transmissions(
                    subdag,
                    &self.solutions,
                    &self.transactions,
                    &self.aborted_transaction_ids,
                )?;
            }
        }

        // Determine the expected timestamp.
        let expected_timestamp = match &self.authority {
            // Beacon blocks do not have a timestamp check.
            Authority::Beacon(..) => self.timestamp(),
            // Quorum blocks use the median timestamp from the subdag.
            Authority::Quorum(subdag) => subdag.timestamp(),
        };

        // Return success.
        Ok((expected_round, expected_height, expected_timestamp))
    }

    /// Ensures the block ratifications are correct.
    fn verify_ratifications(&self, expected_block_reward: u64, expected_puzzle_reward: u64) -> Result<()> {
        let height = self.height();

        // Ensure there are sufficient ratifications.
        ensure!(!self.ratifications.len() >= 2, "Block {height} must contain at least 2 ratifications");

        // Initialize a ratifications iterator.
        let mut ratifications_iter = self.ratifications.iter();

        // Retrieve the block reward from the first block ratification.
        let block_reward = match ratifications_iter.next() {
            Some(Ratify::BlockReward(block_reward)) => *block_reward,
            _ => bail!("Block {height} is invalid - the first ratification must be a block reward"),
        };
        // Retrieve the puzzle reward from the second block ratification.
        let puzzle_reward = match ratifications_iter.next() {
            Some(Ratify::PuzzleReward(puzzle_reward)) => *puzzle_reward,
            _ => bail!("Block {height} is invalid - the second ratification must be a puzzle reward"),
        };

        // Ensure the block reward is correct.
        ensure!(
            block_reward == expected_block_reward,
            "Block {height} has an invalid block reward (found '{block_reward}', expected '{expected_block_reward}')",
        );
        // Ensure the puzzle reward is correct.
        ensure!(
            puzzle_reward == expected_puzzle_reward,
            "Block {height} has an invalid puzzle reward (found '{puzzle_reward}', expected '{expected_puzzle_reward}')",
        );
        Ok(())
    }

    /// Ensures the block solutions are correct.
    fn verify_solutions(
        &self,
        previous_block: &Block<N>,
        current_puzzle: &CoinbasePuzzle<N>,
        current_epoch_challenge: &EpochChallenge<N>,
    ) -> Result<(u128, u128, u64, u64, u64, i64, u64, u64)> {
        let height = self.height();
        let timestamp = self.timestamp();

        let (combined_proof_target, expected_cumulative_proof_target, is_coinbase_target_reached) = match &self
            .solutions
        {
            Some(coinbase) => {
                // Ensure the number of solutions is within the allowed range.
                ensure!(
                    coinbase.len() <= N::MAX_PROVER_SOLUTIONS,
                    "Block {height} contains too many prover solutions (found '{}', expected '{}')",
                    coinbase.len(),
                    N::MAX_PROVER_SOLUTIONS
                );
                // Ensure the solutions are not accepted after the block height at year 10.
                if height > block_height_at_year(N::BLOCK_TIME, 10) {
                    bail!("Solutions are no longer accepted after the block height at year 10.");
                }

                // Ensure the puzzle proof is valid.
                let is_valid =
                    current_puzzle.verify(coinbase, current_epoch_challenge, previous_block.proof_target())?;
                ensure!(is_valid, "Block {height} contains invalid puzzle proof");

                // Compute the combined proof target.
                let combined_proof_target = coinbase.to_combined_proof_target()?;

                // Ensure that the block cumulative proof target is less than the previous block's coinbase target.
                // Note: This is a sanity check, as the cumulative proof target resets to 0 if the
                // coinbase target was reached in this block.
                if self.cumulative_proof_target() >= previous_block.coinbase_target() as u128 {
                    bail!(
                        "The cumulative proof target in block {height} must be less than the previous coinbase target"
                    )
                }

                // Compute the actual cumulative proof target (which can exceed the coinbase target).
                let cumulative_proof_target =
                    previous_block.cumulative_proof_target().saturating_add(combined_proof_target);
                // Determine if the coinbase target is reached.
                let is_coinbase_target_reached = cumulative_proof_target >= previous_block.coinbase_target() as u128;
                // Compute the block cumulative proof target (which cannot exceed the coinbase target).
                let expected_cumulative_proof_target = match is_coinbase_target_reached {
                    true => 0u128,
                    false => cumulative_proof_target,
                };

                (combined_proof_target, expected_cumulative_proof_target, is_coinbase_target_reached)
            }
            None => {
                // Set the combined proof target.
                let combined_proof_target = 0;
                // Determine the cumulative proof target.
                let expected_cumulative_proof_target = previous_block.cumulative_proof_target();

                (combined_proof_target, expected_cumulative_proof_target, false)
            }
        };

        // Compute the expected cumulative weight.
        let expected_cumulative_weight = previous_block.cumulative_weight().saturating_add(combined_proof_target);

        // Construct the next coinbase target.
        let expected_coinbase_target = coinbase_target(
            previous_block.last_coinbase_target(),
            previous_block.last_coinbase_timestamp(),
            timestamp,
            N::ANCHOR_TIME,
            N::NUM_BLOCKS_PER_EPOCH,
            N::GENESIS_COINBASE_TARGET,
        )?;
        // Ensure the proof target is correct.
        let expected_proof_target = proof_target(expected_coinbase_target, N::GENESIS_PROOF_TARGET);

        // Determine the expected last coinbase target.
        let expected_last_coinbase_target = match is_coinbase_target_reached {
            true => expected_coinbase_target,
            false => previous_block.last_coinbase_target(),
        };
        // Determine the expected last coinbase timestamp.
        let expected_last_coinbase_timestamp = match is_coinbase_target_reached {
            true => timestamp,
            false => previous_block.last_coinbase_timestamp(),
        };

        // Calculate the expected coinbase reward.
        let expected_coinbase_reward = coinbase_reward(
            height,
            N::STARTING_SUPPLY,
            N::ANCHOR_HEIGHT,
            N::BLOCK_TIME,
            combined_proof_target,
            u64::try_from(previous_block.cumulative_proof_target())?,
            previous_block.coinbase_target(),
        )?;
        // Compute the expected block reward.
        let expected_block_reward = block_reward(N::STARTING_SUPPLY, N::BLOCK_TIME, expected_coinbase_reward);
        // Compute the expected puzzle reward.
        let expected_puzzle_reward = expected_coinbase_reward.saturating_div(2);

        Ok((
            expected_cumulative_weight,
            expected_cumulative_proof_target,
            expected_coinbase_target,
            expected_proof_target,
            expected_last_coinbase_target,
            expected_last_coinbase_timestamp,
            expected_block_reward,
            expected_puzzle_reward,
        ))
    }

    /// Ensures the block transactions are correct.
    fn verify_transactions(&self) -> Result<()> {
        let height = self.height();

        // Ensure there are transactions.
        ensure!(!self.transactions.is_empty(), "Block {height} must contain at least 1 transaction");

        // Ensure the number of transactions is within the allowed range.
        if self.transactions.len() + self.aborted_transaction_ids.len() > Transactions::<N>::MAX_TRANSACTIONS {
            bail!("Cannot validate a block with more than {} transactions", Transactions::<N>::MAX_TRANSACTIONS);
        }

        // Ensure there are no duplicate transaction IDs.
        if has_duplicates(self.transaction_ids().chain(self.aborted_transaction_ids.iter())) {
            bail!("Found a duplicate transaction in block {height}");
        }

        // Ensure there are no duplicate transition IDs.
        if has_duplicates(self.transition_ids()) {
            bail!("Found a duplicate transition in block {height}");
        }

        /* Input */

        // Ensure there are no duplicate input IDs.
        if has_duplicates(self.input_ids()) {
            bail!("Found a duplicate input ID in block {height}");
        }
        // Ensure there are no duplicate serial numbers.
        if has_duplicates(self.serial_numbers()) {
            bail!("Found a duplicate serial number in block {height}");
        }
        // Ensure there are no duplicate tags.
        if has_duplicates(self.tags()) {
            bail!("Found a duplicate tag in block {height}");
        }

        /* Output */

        // Ensure there are no duplicate output IDs.
        if has_duplicates(self.output_ids()) {
            bail!("Found a duplicate output ID in block {height}");
        }
        // Ensure there are no duplicate commitments.
        if has_duplicates(self.commitments()) {
            bail!("Found a duplicate commitment in block {height}");
        }
        // Ensure there are no duplicate nonces.
        if has_duplicates(self.nonces()) {
            bail!("Found a duplicate nonce in block {height}");
        }

        /* Metadata */

        // Ensure there are no duplicate transition public keys.
        if has_duplicates(self.transition_public_keys()) {
            bail!("Found a duplicate transition public key in block {height}");
        }
        // Ensure there are no duplicate transition commitments.
        if has_duplicates(self.transition_commitments()) {
            bail!("Found a duplicate transition commitment in block {height}");
        }
        Ok(())
    }
}
impl<N: Network> Block<N> {
    /// Computes the transactions root for the block.
    fn compute_transactions_root(&self) -> Result<Field<N>> {
        match self.transactions.to_transactions_root() {
            Ok(transactions_root) => Ok(transactions_root),
            Err(error) => bail!("Failed to compute the transactions root for block {} - {error}", self.height()),
        }
    }

    /// Computes the finalize root for the block.
    fn compute_finalize_root(&self, ratified_finalize_operations: Vec<FinalizeOperation<N>>) -> Result<Field<N>> {
        match self.transactions.to_finalize_root(ratified_finalize_operations) {
            Ok(finalize_root) => Ok(finalize_root),
            Err(error) => bail!("Failed to compute the finalize root for block {} - {error}", self.height()),
        }
    }

    /// Computes the ratifications root for the block.
    fn compute_ratifications_root(&self) -> Result<Field<N>> {
        match self.ratifications.to_ratifications_root() {
            Ok(ratifications_root) => Ok(ratifications_root),
            Err(error) => bail!("Failed to compute the ratifications root for block {} - {error}", self.height()),
        }
    }

    /// Computes the solutions root for the block.
    fn compute_solutions_root(&self) -> Result<Field<N>> {
        match self.solutions {
            Some(ref coinbase) => coinbase.to_accumulator_point(),
            None => Ok(Field::zero()),
        }
    }

    /// Computes the subdag root for the block.
    fn compute_subdag_root(&self) -> Result<Field<N>> {
        match self.authority {
            Authority::Quorum(ref subdag) => subdag.to_subdag_root(),
            Authority::Beacon(_) => Ok(Field::zero()),
        }
    }

    /// Checks that the transmission IDs in the given subdag matches the solutions and transactions in the block.
    pub(super) fn check_subdag_transmissions(
        subdag: &Subdag<N>,
        solutions: &Option<CoinbaseSolution<N>>,
        transactions: &Transactions<N>,
        aborted_transaction_ids: &[N::TransactionID],
    ) -> Result<()> {
        // Prepare an iterator over the solution IDs.
        let mut solutions = solutions.as_ref().map(|s| s.deref()).into_iter().flatten().peekable();
        // Prepare an iterator over the unconfirmed transaction IDs.
        let unconfirmed_transaction_ids = cfg_iter!(transactions)
            .map(|confirmed| confirmed.to_unconfirmed_transaction_id())
            .collect::<Result<Vec<_>>>()?;
        let mut unconfirmed_transaction_ids = unconfirmed_transaction_ids.iter().peekable();

        // Initialize a list of already seen transmission IDs.
        let mut seen_transmission_ids = HashSet::new();

        // Initialize a list of aborted or already-existing solution IDs.
        let mut aborted_or_existing_solution_ids = Vec::new();
        // Initialize a list of aborted or already-existing transaction IDs.
        let mut aborted_or_existing_transaction_ids = Vec::new();

        // Iterate over the transmission IDs.
        for transmission_id in subdag.transmission_ids() {
            // If the transmission ID has already been seen, then continue.
            if !seen_transmission_ids.insert(transmission_id) {
                continue;
            }

            // Process the transmission ID.
            match transmission_id {
                TransmissionID::Ratification => {}
                TransmissionID::Solution(commitment) => {
                    match solutions.peek() {
                        // Check the next solution matches the expected commitment.
                        Some((_, solution)) if solution.commitment() == *commitment => {
                            // Increment the solution iterator.
                            solutions.next();
                        }
                        // Otherwise, add the solution ID to the aborted or existing list.
                        _ => aborted_or_existing_solution_ids.push(commitment),
                    }
                }
                TransmissionID::Transaction(transaction_id) => {
                    match unconfirmed_transaction_ids.peek() {
                        // Check the next transaction matches the expected transaction.
                        Some(expected_id) if transaction_id == *expected_id => {
                            // Increment the unconfirmed transaction ID iterator.
                            unconfirmed_transaction_ids.next();
                        }
                        // Otherwise, add the transaction ID to the aborted or existing list.
                        _ => aborted_or_existing_transaction_ids.push(*transaction_id),
                    }
                }
            }
        }

        // Ensure there are no more solutions in the block.
        ensure!(solutions.next().is_none(), "There exists more solutions than expected.");
        // Ensure there are no more transactions in the block.
        ensure!(unconfirmed_transaction_ids.next().is_none(), "There exists more transactions than expected.");

        // TODO: Move this check to be outside of this method, and check against the ledger for existence.
        // Ensure there are no aborted or existing solution IDs.
        // ensure!(aborted_or_existing_solution_ids.is_empty(), "Block contains aborted or already-existing solutions.");
        // Ensure the aborted transaction IDs match.
        for aborted_transaction_id in aborted_transaction_ids {
            // If the aborted transaction ID is not found, throw an error.
            if !aborted_or_existing_transaction_ids.contains(aborted_transaction_id) {
                bail!(
                    "Block contains an aborted transaction ID that is not found in the subdag (found '{aborted_transaction_id}')"
                );
            }
        }

        Ok(())
    }
}
