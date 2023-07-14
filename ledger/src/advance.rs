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
        // Retrieve the latest round.
        let latest_round = latest_block.round();
        // Retrieve the latest height.
        let latest_height = latest_block.height();
        // Retrieve the latest total supply in microcredits.
        let latest_total_supply = latest_block.total_supply_in_microcredits();
        // Retrieve the latest cumulative weight.
        let latest_cumulative_weight = latest_block.cumulative_weight();

        // Construct the coinbase solution.
        let (coinbase, coinbase_accumulator_point, cumulative_proof_target) = match &candidate_solutions {
            Some(solutions) => {
                // Accumulate the prover solutions into a coinbase solution.
                let coinbase = self.coinbase_puzzle.accumulate_unchecked(&self.latest_epoch_challenge()?, solutions)?;
                // Compute the accumulator point of the coinbase solution.
                let coinbase_accumulator_point = coinbase.to_accumulator_point()?;
                // Compute the cumulative proof target. Using '.sum' here is safe because we sum u64s into a u128.
                let cumulative_proof_target =
                    solutions.iter().map(|s| Ok(s.to_target()? as u128)).sum::<Result<u128>>()?;
                // Output the coinbase solution, coinbase accumulator point, and cumulative proof target.
                (Some(coinbase), coinbase_accumulator_point, cumulative_proof_target)
            }
            None => (None, Field::<N>::zero(), 0u128),
        };

        // Compute the next round number.
        let next_round = latest_round.saturating_add(1);
        // Compute the next height.
        let next_height = latest_height.saturating_add(1);
        // Compute the next cumulative weight.
        let next_cumulative_weight = latest_cumulative_weight.saturating_add(cumulative_proof_target);

        // Construct the finalize state.
        let state = FinalizeGlobalState::new::<N>(
            next_round,
            next_height,
            next_cumulative_weight,
            cumulative_proof_target,
            latest_block.hash(),
        )?;
        // Select the transactions from the memory pool.
        let transactions = self.vm.speculate(state, candidate_transactions.iter())?;

        // Compute the next total supply in microcredits.
        let next_total_supply_in_microcredits = update_total_supply(latest_total_supply, &transactions)?;

        // Checkpoint the timestamp for the next block.
        let next_timestamp = OffsetDateTime::now_utc().unix_timestamp();

        // TODO (raychu86): Pay the provers.
        let (proving_rewards, staking_rewards) = match candidate_solutions {
            Some(prover_solutions) => {
                // Calculate the coinbase reward.
                let coinbase_reward = coinbase_reward(
                    latest_block.last_coinbase_timestamp(),
                    next_timestamp,
                    next_height,
                    N::STARTING_SUPPLY,
                    N::ANCHOR_TIME,
                )?;

                // Calculate the proving rewards.
                let proving_rewards = proving_rewards(prover_solutions, coinbase_reward, cumulative_proof_target)?;
                // Calculate the staking rewards.
                let staking_rewards = Vec::<Ratify<N>>::new();
                // Output the proving and staking rewards.
                (proving_rewards, staking_rewards)
            }
            None => {
                // Output the proving and staking rewards.
                (vec![], vec![])
            }
        };

        // Construct the ratifications.
        let mut ratifications = Vec::<Ratify<N>>::new();
        ratifications.extend_from_slice(&proving_rewards);
        ratifications.extend_from_slice(&staking_rewards);

        // Compute the ratifications root.
        let ratifications_root = *N::merkle_tree_bhp::<RATIFICATIONS_DEPTH>(
            // TODO (howardwu): Formalize the Merklization of each Ratify enum.
            &ratifications
                .iter()
                .map(|r| Ok::<_, Error>(r.to_bytes_le()?.to_bits_le()))
                .collect::<Result<Vec<_>, _>>()?,
        )?
        .root();

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

        // Construct the metadata.
        let metadata = Metadata::new(
            N::ID,
            next_round,
            next_height,
            next_total_supply_in_microcredits,
            next_cumulative_weight,
            cumulative_proof_target,
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
            ratifications_root,
            coinbase_accumulator_point,
            metadata,
        )?;

        // Construct the new block.
        Block::new(private_key, latest_block.hash(), header, transactions, ratifications, coinbase, rng)
    }

    /// Adds the given block as the next block in the ledger.
    pub fn advance_to_next_block(&self, block: &Block<N>) -> Result<()> {
        // Cache the current epoch number.
        let current_epoch_number = self.latest_epoch_number();

        // Acquire the write lock on the current block.
        let mut current_block = self.current_block.write();
        // Update the VM.
        self.vm.add_next_block(block)?;
        // Update the current block.
        *current_block = block.clone();
        // Drop the write lock on the current block.
        drop(current_block);

        // Clears the memory pool of pending solutions that are now invalid.
        if block.coinbase().is_some() {
            self.pending_solutions.write().retain(|puzzle_commitment, _solution| {
                // Ensure the prover solution is still valid.
                match self.contains_puzzle_commitment(puzzle_commitment) {
                    Ok(true) | Err(_) => {
                        trace!("Removed prover solution '{puzzle_commitment}' from the memory pool");
                        false
                    }
                    Ok(false) => true,
                }
            });
        }
        // If this starts a new epoch, clear all unconfirmed solutions from the memory pool.
        if block.epoch_number() > current_epoch_number {
            self.pending_solutions.write().clear();
        }

        // If the block is the start of a new epoch, or the epoch challenge has not been set, update the current epoch challenge.
        if block.height() % N::NUM_BLOCKS_PER_EPOCH == 0 || self.current_epoch_challenge.read().is_none() {
            // Update the current epoch challenge.
            self.current_epoch_challenge.write().clone_from(&self.get_epoch_challenge(block.height()).ok());
        }

        // // If there are block solutions, add them to the pending solutions.
        // if !block.solutions().is_empty() {
        //     // Acquire the write lock for the pending solutions.
        //     let mut pending_solutions = self.pending_solutions.write();
        //     // Iterate through the solutions.
        //     block.solutions().iter().for_each(|solution| {
        //         // Determine if the solution was committed, safely.
        //         let is_committed = self.contains_puzzle_commitment(&solution.commitment()).unwrap_or(true);
        //         // If the solution has not been committed, add it to the pending solutions.
        //         if !is_committed {
        //             // Compute the proof target.
        //             if let Some(proof_target) = solution.to_target() {
        //                 pending_solutions.insert(solution.commitment(), (solution, proof_target));
        //             }
        //         }
        //     });
        // }

        info!("Advanced to block {}", block.height());
        Ok(())
    }
}

impl<N: Network, C: ConsensusStorage<N>> Ledger<N, C> {
    /// Returns a candidate set of unconfirmed solutions for inclusion in a block.
    pub fn candidate_solutions(
        &self,
        pending_solutions: IndexMap<PuzzleCommitment<N>, (ProverSolution<N>, u64)>,
        latest_height: u32,
        latest_proof_target: u64,
        latest_coinbase_target: u64,
    ) -> Result<Option<Vec<ProverSolution<N>>>> {
        // If the latest height is greater than or equal to the anchor height at year 10, then return 'None'.
        if latest_height >= anchor_block_height(N::ANCHOR_TIME, 10) {
            return Ok(None);
        }

        // Filter the solutions by the latest proof target, ensure they are unique, and rank in descending order of proof target.
        let candidate_solutions: Vec<_> = pending_solutions
            .iter()
            .filter(|(_, (_, proof_target))| *proof_target >= latest_proof_target)
            .filter(|(_, (solution, _))| {
                // Ensure the prover solution is not already in the ledger.
                match self.contains_puzzle_commitment(&solution.commitment()) {
                    Ok(true) => false,
                    Ok(false) => true,
                    Err(error) => {
                        error!("Failed to check if prover solution {error} is in the ledger");
                        false
                    }
                }
            })
            .sorted_by(|a, b| b.1.1.cmp(&a.1.1))
            .map(|(_, v)| v.0)
            .unique_by(|s| s.commitment())
            .take(256)
            .collect();

        // Compute the cumulative proof target of the prover solutions as a u128.
        let cumulative_proof_target: u128 = candidate_solutions.iter().try_fold(0u128, |cumulative, solution| {
            cumulative
                .checked_add(solution.to_target()? as u128)
                .ok_or_else(|| anyhow!("Cumulative proof target overflowed"))
        })?;

        // Return the prover solutions if the cumulative target is greater than or equal to the coinbase target.
        match cumulative_proof_target >= latest_coinbase_target as u128 {
            true => Ok(Some(candidate_solutions)),
            false => Ok(None),
        }
    }

    // TODO (raychu86): Remove PrivateKey and rng inputs.
    /// Returns the next block in the ledger for the given committed_subdag.
    pub fn prepare_advance_to_next_block_bft<R: Rng + CryptoRng>(
        &self,
        committed_subdag: BTreeMap<u64, Vec<BatchCertificate<N>>>,
        transmissions: IndexMap<TransmissionID<N>, Transmission<N>>,
        private_key: &PrivateKey<N>,
        rng: &mut R,
    ) -> Result<Block<N>> {
        // Retrieve the leader certificate in the round.
        let leader_certificate = match committed_subdag.iter().next_back() {
            Some((_, value)) => {
                ensure!(value.len() == 1, "There should only be one leader certificate per round");
                value[0].clone()
            }
            None => bail!("Missing leader certificate"),
        };

        // Retrieve the latest state root.
        let latest_state_root = *self.latest_state_root();
        // Retrieve the latest block.
        let latest_block = self.latest_block();
        // Retrieve the latest height.
        let latest_height = latest_block.height();
        // Retrieve the latest total supply in microcredits.
        let latest_total_supply = latest_block.total_supply_in_microcredits();
        // Retrieve the latest cumulative weight.
        let latest_cumulative_weight = latest_block.cumulative_weight();
        // Retrieve the latest proof target.
        let latest_proof_target = latest_block.proof_target();
        // Retrieve the latest coinbase target.
        let latest_coinbase_target = latest_block.coinbase_target();

        // TODO (raychu86): Check that the `committed_subdag` translates properly into the set of transmissions. For now we can assume this is correct.

        // Extract transactions.
        let mut transactions: Vec<Transaction<N>> = Vec::new();

        // Extract prover solutions.
        let mut solutions = IndexMap::new();

        // Extract ratifications.
        let mut ratifications = Vec::new();

        // Extract the transactions, prover solutions, and ratifications.
        for (_, transmission) in transmissions.into_iter() {
            match transmission {
                Transmission::Transaction(transaction) => {
                    transactions.push(transaction.deserialize_blocking()?);
                }
                Transmission::Solution(solution) => {
                    let solution = solution.deserialize_blocking()?;
                    let proof_target = solution.to_target()?;
                    // TODO (raychu86): Do we check if the target is sufficient? Or if the solution is valid for the epoch?
                    solutions.insert(solution.commitment(), (solution, proof_target));
                }
                Transmission::Ratification => {
                    // ratifications.push(ratification.into());
                }
            }
        }

        // Fetch the pending solutions.
        let mut pending_solutions = self.latest_pending_solutions();
        // Add the new solutions to the pending solutions (in memory).
        pending_solutions.extend(solutions);

        // Construct the candidate solutions from new set of pending solutions.
        let candidate_solutions =
            self.candidate_solutions(pending_solutions, latest_height, latest_proof_target, latest_coinbase_target)?;

        // Construct the coinbase solution.
        let (coinbase, coinbase_accumulator_point, cumulative_proof_target) = match &candidate_solutions {
            Some(solutions) => {
                // Accumulate the prover solutions into a coinbase solution.
                let coinbase = self.coinbase_puzzle.accumulate_unchecked(&self.latest_epoch_challenge()?, solutions)?;
                // Compute the accumulator point of the coinbase solution.
                let coinbase_accumulator_point = coinbase.to_accumulator_point()?;
                // Compute the cumulative proof target. Using '.sum' here is safe because we sum u64s into a u128.
                let cumulative_proof_target =
                    solutions.iter().map(|s| Ok(s.to_target()? as u128)).sum::<Result<u128>>()?;
                // Output the coinbase solution, coinbase accumulator point, and cumulative proof target.
                (Some(coinbase), coinbase_accumulator_point, cumulative_proof_target)
            }
            None => (None, Field::<N>::zero(), 0u128),
        };

        // Compute the next round number.
        let next_round = leader_certificate.round();
        // Compute the next height.
        let next_height = latest_height.saturating_add(1);
        // Compute the next cumulative weight.
        let next_cumulative_weight = latest_cumulative_weight.saturating_add(cumulative_proof_target);

        // Construct the finalize state.
        let state = FinalizeGlobalState::new::<N>(
            next_round,
            next_height,
            next_cumulative_weight,
            cumulative_proof_target,
            latest_block.hash(),
        )?;

        // Select the transactions from the memory pool.
        let transactions = self.vm.speculate(state, transactions.iter())?;

        // Compute the next total supply in microcredits.
        let next_total_supply_in_microcredits = update_total_supply(latest_total_supply, &transactions)?;

        // Checkpoint the timestamp for the next block as the median timestamp of the certificates.
        let next_timestamp = leader_certificate.median_timestamp();

        // TODO (raychu86): Pay the provers.
        let (proving_rewards, staking_rewards) = match candidate_solutions {
            Some(prover_solutions) => {
                // Calculate the coinbase reward.
                let coinbase_reward = coinbase_reward(
                    self.last_coinbase_timestamp(),
                    next_timestamp,
                    next_height,
                    N::STARTING_SUPPLY,
                    N::ANCHOR_TIME,
                )?;

                // Calculate the proving rewards.
                let proving_rewards = proving_rewards(prover_solutions, coinbase_reward, cumulative_proof_target)?;
                // Calculate the staking rewards.
                let staking_rewards = Vec::<Ratify<N>>::new();
                // Output the proving and staking rewards.
                (proving_rewards, staking_rewards)
            }
            None => {
                // Output the proving and staking rewards.
                (vec![], vec![])
            }
        };

        // Construct the ratifications.
        ratifications.extend_from_slice(&proving_rewards);
        ratifications.extend_from_slice(&staking_rewards);

        // Compute the ratifications root.
        let ratifications_root = *N::merkle_tree_bhp::<RATIFICATIONS_DEPTH>(
            // TODO (howardwu): Formalize the Merklization of each Ratify enum.
            &ratifications
                .iter()
                .map(|r| Ok::<_, Error>(r.to_bytes_le()?.to_bits_le()))
                .collect::<Result<Vec<_>, _>>()?,
        )?
        .root();

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

        // Construct the metadata.
        let metadata = Metadata::new(
            N::ID,
            next_round,
            next_height,
            next_total_supply_in_microcredits,
            next_cumulative_weight,
            cumulative_proof_target,
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
            ratifications_root,
            coinbase_accumulator_point,
            metadata,
        )?;

        // Construct the new block.
        Block::new(private_key, latest_block.hash(), header, transactions, ratifications, coinbase, rng)
    }
}
