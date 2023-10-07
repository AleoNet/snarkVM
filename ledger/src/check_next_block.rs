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
        if let Some(coinbase) = block.coinbase() {
            for puzzle_commitment in coinbase.puzzle_commitments() {
                if self.contains_puzzle_commitment(puzzle_commitment)? {
                    bail!("Puzzle commitment {puzzle_commitment} already exists in the ledger");
                }
            }
        }

        // Ensure each transaction is well-formed and unique.
        // TODO: this intermediate allocation shouldn't be necessary; this is most likely https://github.com/rust-lang/rust/issues/89418.
        let transactions = block.transactions().iter().collect::<Vec<_>>();
        cfg_iter!(transactions).try_for_each(|transaction| {
            // Construct the rejected ID.
            let rejected_id = match transaction {
                ConfirmedTransaction::AcceptedDeploy(..) | ConfirmedTransaction::AcceptedExecute(..) => None,
                ConfirmedTransaction::RejectedDeploy(_, _, rejected) => Some(rejected.to_id()?),
                ConfirmedTransaction::RejectedExecute(_, _, rejected) => Some(rejected.to_id()?),
            };

            self.check_transaction_basic(*transaction, rejected_id)
                .map_err(|e| anyhow!("Invalid transaction found in the transactions list: {e}"))
        })?;

        // Ensure the block is correct.
        block.verify(
            &self.latest_block(),
            self.latest_state_root(),
            &self.latest_committee()?,
            self.coinbase_puzzle(),
            &self.latest_epoch_challenge()?,
            OffsetDateTime::now_utc().unix_timestamp(),
        )?;

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

        // Reconstruct the unconfirmed transactions to verify the speculation.
        let unconfirmed_transactions = block
            .transactions()
            .iter()
            .map(|tx| match tx {
                // Pass through the accepted deployment and execution transactions.
                ConfirmedTransaction::AcceptedDeploy(_, tx, _) | ConfirmedTransaction::AcceptedExecute(_, tx, _) => {
                    Ok(tx.clone())
                }
                // Reconstruct the unconfirmed deployment transaction.
                ConfirmedTransaction::RejectedDeploy(_, fee_transaction, rejected) => Transaction::from_deployment(
                    rejected.program_owner().copied().ok_or(anyhow!("Missing the program owner"))?,
                    rejected.deployment().cloned().ok_or(anyhow!("Missing the deployment"))?,
                    fee_transaction.fee_transition().ok_or(anyhow!("Missing the fee transition"))?,
                ),
                // Reconstruct the unconfirmed execution transaction.
                ConfirmedTransaction::RejectedExecute(_, fee_transaction, rejected) => Transaction::from_execution(
                    rejected.execution().cloned().ok_or(anyhow!("Missing the execution"))?,
                    fee_transaction.fee_transition(),
                ),
            })
            .collect::<Result<Vec<_>>>()?;

        // Speculate over the unconfirmed transactions.
        let (confirmed_transactions, _) =
            self.vm.speculate(state, block.ratifications(), block.coinbase(), unconfirmed_transactions.iter())?;

        // Ensure the transactions after speculation match.
        if block.transactions() != &confirmed_transactions {
            bail!("The transactions after speculation do not match the transactions in the block");
        }

        Ok(())
    }
}
