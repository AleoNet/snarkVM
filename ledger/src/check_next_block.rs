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

impl<N: Network, C: ConsensusStorage<N>> Ledger<N, C> {
    /// Checks the given block is valid next block.
    pub fn check_next_block(&self, block: &Block<N>) -> Result<()> {
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
        // TODO: this intermediate allocation shouldn't be necessary; this is most likely https://github.com/rust-lang/rust/issues/89418.
        let transactions = block.transactions().iter().collect::<Vec<_>>();
        cfg_iter!(transactions).try_for_each(|transaction| {
            self.check_transaction_basic(*transaction, transaction.to_rejected_id()?)
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

        // Reconstruct the candidate ratifications to verify the speculation.
        let candidate_ratifications = block.ratifications().iter().cloned().collect::<Vec<_>>();

        // Reconstruct the unconfirmed transactions to verify the speculation.
        let unconfirmed_transactions = block
            .transactions()
            .iter()
            .map(|confirmed| confirmed.to_unconfirmed_transaction())
            .collect::<Result<Vec<_>>>()?;

        // Speculate over the unconfirmed transactions.
        let (ratifications, confirmed_transactions, aborted_transaction_ids, ratified_finalize_operations) =
            self.vm.speculate(state, &candidate_ratifications, block.solutions(), unconfirmed_transactions.iter())?;
        // Ensure there are no aborted transaction IDs from this speculation.
        // Note: There should be no aborted transactions, because we are checking a block,
        // where any aborted transactions should be in the aborted transaction ID list, not in transactions.
        ensure!(aborted_transaction_ids.is_empty(), "Aborted transactions found in the block (from speculation)");

        // Ensure the ratifications after speculation match.
        if block.ratifications() != &ratifications {
            bail!("The ratifications after speculation do not match the ratifications in the block");
        }
        // Ensure the transactions after speculation match.
        if block.transactions() != &confirmed_transactions {
            bail!("The transactions after speculation do not match the transactions in the block");
        }

        // Ensure the block is correct.
        block.verify(
            &self.latest_block(),
            self.latest_state_root(),
            &self.latest_committee()?,
            self.coinbase_puzzle(),
            &self.latest_epoch_challenge()?,
            OffsetDateTime::now_utc().unix_timestamp(),
            ratified_finalize_operations,
        )?;

        Ok(())
    }
}
