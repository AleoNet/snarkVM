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
    /// Returns a candidate for the next block in the ledger.
    pub fn prepare_advance_to_next_block<R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        candidate_transactions: Vec<Transaction<N>>,
        candidate_solutions: Option<Vec<ProverSolution<N>>>,
        rng: &mut R,
    ) -> Result<Block<N>> {
        // Retrieve the latest state root.
        let latest_state_root = *self.latest_state_root();
        // Retrieve the latest block.
        let latest_block = self.latest_block();
        // Retrieve the latest height.
        let latest_height = latest_block.height();
        // Retrieve the latest total supply in microcredits.
        let latest_total_supply_in_microcredits = latest_block.total_supply_in_microcredits();
        // Retrieve the latest cumulative weight.
        let latest_cumulative_weight = latest_block.cumulative_weight();

        // Select the transactions from the memory pool.
        let transactions = self.vm.speculate(candidate_transactions.iter())?;

        // TODO (raychu86): Clean this up or create a `total_supply_delta` in `Transactions`.
        // Calculate the new total supply of microcredits after the block.
        let mut new_total_supply_in_microcredits = latest_total_supply_in_microcredits;
        for confirmed_tx in transactions.iter() {
            // Subtract the fee from the total supply.
            let fee = confirmed_tx.fee()?;
            new_total_supply_in_microcredits = new_total_supply_in_microcredits
                .checked_sub(*fee)
                .ok_or_else(|| anyhow!("Fee exceeded total supply of credits"))?;

            // If the transaction is a coinbase, add the amount to the total supply.
            if confirmed_tx.is_coinbase() {
                if let Transaction::Execute(_, execution, _) = confirmed_tx.transaction() {
                    // Loop over coinbase transitions and accumulate the amounts.
                    for transition in execution.transitions().filter(|t| t.is_coinbase()) {
                        // Extract the amount from the second input (amount) if it exists.
                        let amount = transition
                            .inputs()
                            .get(1)
                            .and_then(|input| match input {
                                Input::Public(_, Some(Plaintext::Literal(Literal::U64(amount), _))) => Some(amount),
                                _ => None,
                            })
                            .ok_or_else(|| {
                                anyhow!("Invalid coinbase transaction: Missing public input in 'credits.aleo/mint'")
                            })?;

                        // Add the public amount minted to the total supply.
                        new_total_supply_in_microcredits = new_total_supply_in_microcredits
                            .checked_add(**amount)
                            .ok_or_else(|| anyhow!("Total supply of microcredits overflowed"))?;
                    }
                } else {
                    bail!("Invalid coinbase transaction");
                }
            }
        }

        // Construct the coinbase solution.
        let (coinbase, coinbase_accumulator_point) = match &candidate_solutions {
            Some(prover_solutions) => {
                let epoch_challenge = self.latest_epoch_challenge()?;
                let coinbase_solution =
                    self.coinbase_puzzle.accumulate_unchecked(&epoch_challenge, prover_solutions)?;
                let coinbase_accumulator_point = coinbase_solution.to_accumulator_point()?;

                (Some(coinbase_solution), coinbase_accumulator_point)
            }
            None => (None, Field::<N>::zero()),
        };

        // Fetch the next round state.
        let next_timestamp = OffsetDateTime::now_utc().unix_timestamp();
        let next_height = latest_height.saturating_add(1);
        let next_round = latest_block.round().saturating_add(1);

        // TODO (raychu86): Pay the provers. Currently we do not pay the provers with the `credits.aleo` program
        //  and instead, will track prover leaderboards via the `coinbase_solution` in each block.
        let block_cumulative_proof_target = if let Some(prover_solutions) = candidate_solutions {
            // Calculate the coinbase reward.
            let coinbase_reward = coinbase_reward(
                latest_block.last_coinbase_timestamp(),
                next_timestamp,
                next_height,
                N::STARTING_SUPPLY,
                N::ANCHOR_TIME,
            )?;

            // Compute the cumulative proof target of the prover solutions as a u128.
            let block_cumulative_proof_target: u128 =
                prover_solutions.iter().try_fold(0u128, |cumulative, solution| {
                    cumulative
                        .checked_add(solution.to_target()? as u128)
                        .ok_or_else(|| anyhow!("Cumulative proof target overflowed"))
                })?;

            // Calculate the rewards for the individual provers.
            let mut prover_rewards: Vec<(Address<N>, u64)> = Vec::new();
            for prover_solution in prover_solutions {
                // Prover compensation is defined as:
                //   1/2 * coinbase_reward * (prover_target / cumulative_prover_target)
                //   = (coinbase_reward * prover_target) / (2 * cumulative_prover_target)

                // Compute the numerator.
                let numerator = (coinbase_reward as u128)
                    .checked_mul(prover_solution.to_target()? as u128)
                    .ok_or_else(|| anyhow!("Prover reward numerator overflowed"))?;

                // Compute the denominator.
                let denominator = block_cumulative_proof_target
                    .checked_mul(2)
                    .ok_or_else(|| anyhow!("Prover reward denominator overflowed"))?;

                // Compute the prover reward.
                let prover_reward = u64::try_from(
                    numerator.checked_div(denominator).ok_or_else(|| anyhow!("Prover reward overflowed"))?,
                )?;

                prover_rewards.push((prover_solution.address(), prover_reward));
            }

            block_cumulative_proof_target
        } else {
            0u128
        };

        // Construct the next coinbase target.
        let next_coinbase_target = coinbase_target(
            latest_block.last_coinbase_target(),
            latest_block.last_coinbase_timestamp(),
            next_timestamp,
            N::ANCHOR_TIME,
            N::NUM_BLOCKS_PER_EPOCH,
            N::GENESIS_COINBASE_TARGET,
        )?;

        // Construct the next proof target.
        let next_proof_target = proof_target(next_coinbase_target, N::GENESIS_PROOF_TARGET);

        // Construct the next last coinbase target and next last coinbase timestamp.
        let (next_last_coinbase_target, next_last_coinbase_timestamp) = match coinbase {
            Some(_) => (next_coinbase_target, next_timestamp),
            None => (latest_block.last_coinbase_target(), latest_block.last_coinbase_timestamp()),
        };

        // Construct the new cumulative weight.
        let cumulative_weight = latest_cumulative_weight.saturating_add(block_cumulative_proof_target);

        // Construct the metadata.
        let metadata = Metadata::new(
            N::ID,
            next_round,
            next_height,
            new_total_supply_in_microcredits,
            cumulative_weight,
            next_coinbase_target,
            next_proof_target,
            next_last_coinbase_target,
            next_last_coinbase_timestamp,
            next_timestamp,
        )?;

        // Construct the header.
        let header = Header::from(
            latest_state_root,
            transactions.to_transactions_root()?,
            transactions.to_finalize_root()?,
            coinbase_accumulator_point,
            metadata,
        )?;

        // Construct the new block.
        Block::new(private_key, latest_block.hash(), header, transactions, coinbase, rng)
    }

    /// Adds the given block as the next block in the ledger.
    pub fn advance_to_next_block(&self, block: &Block<N>) -> Result<()> {
        // Acquire the write lock on the current block.
        let mut current_block = self.current_block.write();
        // Update the VM.
        self.vm.add_next_block(block)?;
        // Update the current block.
        *current_block = block.clone();
        // Drop the write lock on the current block.
        drop(current_block);

        // If the block is the start of a new epoch, or the epoch challenge has not been set, update the current epoch challenge.
        if block.height() % N::NUM_BLOCKS_PER_EPOCH == 0 || self.current_epoch_challenge.read().is_none() {
            // Update the current epoch challenge.
            self.current_epoch_challenge.write().clone_from(&self.get_epoch_challenge(block.height()).ok());
        }

        Ok(())
    }
}
