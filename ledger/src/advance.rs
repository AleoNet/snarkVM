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
    /// Returns a candidate for the next block in the ledger, using a committed subdag and its transmissions.
    pub fn prepare_advance_to_next_block_with_bft(
        &self,
        _committed_subdag: Subdag<N>,
        transmissions: IndexMap<TransmissionID<N>, Transmission<N>>,
    ) -> Result<Block<N>> {
        // Initialize a fixed seed RNG.
        let rng = &mut rand_chacha::ChaChaRng::from_seed([0u8; 32]);
        // Sample a fixed dummy private key, as we don't need a real one in this case.
        let private_key = PrivateKey::<N>::new(rng)?;

        // Decouple the transmissions into ratifications, solutions, and transactions.
        let (_ratifications, solutions, transactions) = decouple_transmissions(transmissions.into_iter())?;
        // Construct the candidate block.
        self.prepare_advance_to_next_block(&private_key, solutions, transactions, rng)
    }

    /// Returns a candidate for the next block in the ledger.
    pub fn prepare_advance_to_next_block<R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        solutions: Vec<ProverSolution<N>>,
        transactions: Vec<Transaction<N>>,
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
        // Retrieve the latest cumulative proof target.
        let latest_cumulative_proof_target = latest_block.cumulative_proof_target();
        // Retrieve the latest coinbase target.
        let latest_coinbase_target = latest_block.coinbase_target();

        // Construct the solutions.
        let (coinbase, coinbase_accumulator_point, proof_targets, combined_proof_target) = match solutions.is_empty() {
            true => (None, Field::<N>::zero(), Default::default(), 0u128),
            false => {
                // Accumulate the prover solutions.
                let (coinbase, coinbase_accumulator_point) =
                    self.coinbase_puzzle.accumulate_unchecked(&self.latest_epoch_challenge()?, &solutions)?;
                // Compute the proof targets, with the corresponding addresses.
                let proof_targets =
                    solutions.iter().map(|s| Ok((s.address(), s.to_target()? as u128))).collect::<Result<Vec<_>>>()?;
                // Compute the combined proof target. Using '.sum' here is safe because we sum u64s into a u128.
                let combined_proof_target = proof_targets.iter().map(|(_, t)| t).sum::<u128>();
                // Output the solutions, coinbase accumulator point, and combined proof target.
                (Some(coinbase), coinbase_accumulator_point, proof_targets, combined_proof_target)
            }
        };

        // Compute the next round number.
        let next_round = latest_round.saturating_add(1);
        // Compute the next height.
        let next_height = latest_height.saturating_add(1);
        // Compute the next cumulative weight.
        let next_cumulative_weight = latest_cumulative_weight.saturating_add(combined_proof_target);
        // Compute the next cumulative proof target.
        let next_cumulative_proof_target = latest_cumulative_proof_target.saturating_add(combined_proof_target);
        // Determine if the coinbase target is reached.
        let is_coinbase_target_reached = next_cumulative_proof_target >= latest_coinbase_target as u128;
        // Update the next cumulative proof target, if necessary.
        let next_cumulative_proof_target = match is_coinbase_target_reached {
            true => 0,
            false => next_cumulative_proof_target,
        };

        // Construct the finalize state.
        let state = FinalizeGlobalState::new::<N>(
            next_round,
            next_height,
            next_cumulative_weight,
            next_cumulative_proof_target,
            latest_block.hash(),
        )?;
        // Select the transactions from the memory pool.
        let transactions = self.vm.speculate(state, transactions.iter())?;

        // Compute the next total supply in microcredits.
        let next_total_supply_in_microcredits = update_total_supply(latest_total_supply, &transactions)?;

        // Checkpoint the timestamp for the next block.
        let next_timestamp = OffsetDateTime::now_utc().unix_timestamp();

        // TODO (raychu86): Pay the provers.
        let (proving_rewards, staking_rewards) = match proof_targets.is_empty() {
            true => {
                // Output the proving and staking rewards.
                (vec![], vec![])
            }
            false => {
                // Calculate the coinbase reward.
                let remaining_coinbase_target =
                    latest_coinbase_target.saturating_sub(u64::try_from(latest_cumulative_proof_target)?);
                let coinbase_reward = coinbase_reward(
                    next_height,
                    N::STARTING_SUPPLY,
                    N::ANCHOR_TIME,
                    N::BLOCK_TIME,
                    combined_proof_target,
                    remaining_coinbase_target,
                    latest_coinbase_target,
                )?;
                // Calculate the proving rewards.
                let proving_rewards = proving_rewards(proof_targets, coinbase_reward, combined_proof_target);
                // Calculate the staking rewards.
                let staking_rewards = Vec::<Ratify<N>>::new();
                // Output the proving and staking rewards.
                (proving_rewards, staking_rewards)
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
        let (next_last_coinbase_target, next_last_coinbase_timestamp) = match is_coinbase_target_reached {
            true => (next_coinbase_target, next_timestamp),
            false => (latest_block.last_coinbase_target(), latest_block.last_coinbase_timestamp()),
        };

        // Construct the metadata.
        let metadata = Metadata::new(
            N::ID,
            next_round,
            next_height,
            next_total_supply_in_microcredits,
            next_cumulative_weight,
            next_cumulative_proof_target,
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
        Block::new_beacon(private_key, latest_block.hash(), header, transactions, ratifications, coinbase, rng)
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
