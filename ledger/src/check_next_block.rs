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

use super::*;

use rand::{rngs::StdRng, SeedableRng};

impl<N: Network, C: ConsensusStorage<N>> Ledger<N, C> {
    /// Checks the given block is valid next block.
    pub fn check_next_block<R: CryptoRng + Rng>(&self, block: &Block<N>, rng: &mut R) -> Result<()> {
        let height = block.height();

        // Ensure the block hash does not already exist.
        if self.contains_block_hash(&block.hash())? {
            bail!("Block hash '{}' already exists in the ledger", block.hash())
        }

        // Ensure the block height does not already exist.
        if self.contains_block_height(block.height())? {
            bail!("Block height '{height}' already exists in the ledger")
        }

        // Ensure the solutions do not already exist.
        if let Some(solutions) = block.solutions() {
            for puzzle_commitment in solutions.puzzle_commitments() {
                if self.contains_puzzle_commitment(puzzle_commitment)? {
                    bail!("Puzzle commitment {puzzle_commitment} already exists in the ledger");
                }
            }
        }

        // Ensure each transaction is well-formed and unique.
        let transactions = block.transactions();
        let rngs = (0..transactions.len()).map(|_| StdRng::from_seed(rng.gen())).collect::<Vec<_>>();
        cfg_iter!(transactions).zip(rngs).try_for_each(|(transaction, mut rng)| {
            self.check_transaction_basic(transaction, transaction.to_rejected_id()?, &mut rng)
                .map_err(|e| anyhow!("Invalid transaction found in the transactions list: {e}"))
        })?;

        // TODO (howardwu): Remove this after moving the total supply into credits.aleo.
        {
            // // Retrieve the latest total supply.
            // let latest_total_supply = self.latest_total_supply_in_microcredits();
            // // Retrieve the block reward from the first block ratification.
            // let block_reward = match block.ratifications()[0] {
            //     Ratify::BlockReward(block_reward) => block_reward,
            //     _ => bail!("Block {height} is invalid - the first ratification must be a block reward"),
            // };
            // // Retrieve the puzzle reward from the second block ratification.
            // let puzzle_reward = match block.ratifications()[1] {
            //     Ratify::PuzzleReward(puzzle_reward) => puzzle_reward,
            //     _ => bail!("Block {height} is invalid - the second ratification must be a puzzle reward"),
            // };
            // // Compute the next total supply in microcredits.
            // let next_total_supply_in_microcredits =
            //     update_total_supply(latest_total_supply, block_reward, puzzle_reward, block.transactions())?;
            // // Ensure the total supply in microcredits is correct.
            // if next_total_supply_in_microcredits != block.total_supply_in_microcredits() {
            //     bail!("Invalid total supply in microcredits")
            // }
        }

        // Construct the finalize state.
        let state = FinalizeGlobalState::new::<N>(
            block.round(),
            block.height(),
            block.cumulative_weight(),
            block.cumulative_proof_target(),
            block.previous_hash(),
        )?;

        // Ensure speculation over the unconfirmed transactions is correct.
        let ratified_finalize_operations =
            self.vm.check_speculate(state, block.ratifications(), block.solutions(), block.transactions())?;

        // Get the round number for the previous committee. Note, we subtract 2 from odd rounds,
        // because committees are updated in even rounds.
        let previous_round = match block.round() % 2 == 0 {
            true => block.round().saturating_sub(1),
            false => block.round().saturating_sub(2),
        };
        // Get the committee lookback round.
        let committee_lookback_round = previous_round.saturating_sub(Committee::<N>::COMMITTEE_LOOKBACK_RANGE);
        // Retrieve the committee lookback.
        let committee_lookback = self
            .get_committee_for_round(committee_lookback_round)?
            .ok_or(anyhow!("Failed to fetch committee for round {committee_lookback_round}"))?;

        // Ensure the block is correct.
        let expected_existing_transaction_ids = block.verify(
            &self.latest_block(),
            self.latest_state_root(),
            &committee_lookback,
            self.coinbase_puzzle(),
            &self.latest_epoch_challenge()?,
            OffsetDateTime::now_utc().unix_timestamp(),
            ratified_finalize_operations,
        )?;

        // Ensure that each existing transaction id from the block exists in the ledger.
        for existing_transaction_id in expected_existing_transaction_ids {
            if !self.contains_transaction_id(&existing_transaction_id)? {
                bail!("Transaction ID '{existing_transaction_id}' does not exist in the ledger");
            }
        }

        Ok(())
    }
}
