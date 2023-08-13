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
        // Ensure the previous block hash is correct.
        if self.latest_hash() != block.previous_hash() {
            bail!("The next block has an incorrect previous block hash")
        }

        // Ensure the block hash does not already exist.
        if self.contains_block_hash(&block.hash())? {
            bail!("Block hash '{}' already exists in the ledger", block.hash())
        }

        // Ensure the next block height is correct.
        if self.latest_height() > 0 && self.latest_height() + 1 != block.height() {
            bail!("The next block has an incorrect block height")
        }

        // Ensure the block height does not already exist.
        if self.contains_block_height(block.height())? {
            bail!("Block height '{}' already exists in the ledger", block.height())
        }

        // Ensure the next block timestamp is after the current block timestamp.
        if self.latest_height() > 0 && block.timestamp() <= self.latest_timestamp() {
            bail!("The next block timestamp is before the current timestamp")
        }

        // Ensure the next block round and block timestamp are correct.
        match block.authority() {
            Authority::Beacon(..) => {
                // Ensure the next beacon block round is correct.
                if self.latest_round() > 0 && self.latest_round() + 1 != block.round() {
                    bail!("The next beacon block has an incorrect round number")
                }
            }
            Authority::Quorum(subdag) => {
                // Ensure the next quorum block round is correct.
                if block.round() != subdag.anchor_round() {
                    bail!("The next quorum block has an incorrect round number")
                }
                // Ensure the next block timestamp is the median timestamp from the subdag.
                if block.timestamp() != subdag.timestamp() {
                    bail!("The next block timestamp must be the median timestamp from the subdag")
                }
            }
        }

        // Ensure there are no duplicate transition IDs.
        if has_duplicates(block.transition_ids()) {
            bail!("Found duplicate transition in the block");
        }

        /* Input */

        // Ensure there are no duplicate input IDs.
        if has_duplicates(block.input_ids()) {
            bail!("Found duplicate input IDs in the block");
        }

        // Ensure there are no duplicate serial numbers.
        if has_duplicates(block.serial_numbers()) {
            bail!("Found duplicate serial numbers in the block");
        }

        // Ensure there are no duplicate tags.
        if has_duplicates(block.tags()) {
            bail!("Found duplicate tags in the block");
        }

        /* Output */

        // Ensure there are no duplicate output IDs.
        if has_duplicates(block.output_ids()) {
            bail!("Found duplicate output IDs in the block");
        }

        // Ensure there are no duplicate commitments.
        if has_duplicates(block.commitments()) {
            bail!("Found duplicate commitments in the block");
        }

        // Ensure there are no duplicate nonces.
        if has_duplicates(block.nonces()) {
            bail!("Found duplicate nonces in the block");
        }

        /* Metadata */

        // Ensure there are no duplicate transition public keys.
        if has_duplicates(block.transition_public_keys()) {
            bail!("Found duplicate transition public keys in the block");
        }

        // Ensure there are no duplicate transition commitments.
        if has_duplicates(block.transition_commitments()) {
            bail!("Found duplicate transition commitments in the block");
        }

        /* Block Header */

        // Ensure the block header is valid.
        if !block.header().is_valid() {
            bail!("Invalid block header: {:?}", block.header());
        }

        // Retrieve the latest total supply.
        let latest_total_supply = self.latest_total_supply_in_microcredits();
        // Compute the next total supply in microcredits.
        let next_total_supply_in_microcredits = update_total_supply(latest_total_supply, block.transactions())?;
        // Ensure the total supply in microcredits is correct.
        if next_total_supply_in_microcredits != block.total_supply_in_microcredits() {
            bail!("Invalid total supply in microcredits")
        }

        // Check the last coinbase members in the block.
        match block.coinbase() {
            Some(coinbase) => {
                // Compute the combined proof target.
                let combined_proof_target = coinbase.to_combined_proof_target()?;
                // Ensure that the cumulative weight includes the next block's combined proof target.
                if block.cumulative_weight() != self.latest_cumulative_weight().saturating_add(combined_proof_target) {
                    bail!("The cumulative weight does not include the block combined proof target")
                }
                // Ensure that the block cumulative proof target is less than the latest coinbase target.
                // Note: This is a sanity check, as the cumulative proof target resets to 0 if the
                // coinbase target was reached in this block.
                if block.cumulative_proof_target() >= self.latest_coinbase_target() as u128 {
                    bail!("The block cumulative proof target is greater than or equal to the latest coinbase target")
                }
                // Compute the actual cumulative proof target (which can exceed the coinbase target).
                let cumulative_proof_target =
                    self.latest_cumulative_proof_target().saturating_add(combined_proof_target);
                // Determine if the coinbase target is reached.
                let is_coinbase_target_reached = cumulative_proof_target >= self.latest_coinbase_target() as u128;
                // Compute the block cumulative proof target (which cannot exceed the coinbase target).
                let cumulative_proof_target = match is_coinbase_target_reached {
                    true => 0u128,
                    false => cumulative_proof_target,
                };
                // Ensure that the cumulative proof target is correct.
                if block.cumulative_proof_target() != cumulative_proof_target {
                    bail!("The cumulative proof target does not match the expected cumulative proof target")
                }
                // Ensure the last coinbase target and last coinbase height are correct.
                if is_coinbase_target_reached {
                    // Ensure the last coinbase target matches the coinbase target.
                    if block.last_coinbase_target() != block.coinbase_target() {
                        bail!("The last coinbase target does not match the coinbase target")
                    }
                    // Ensure the last coinbase height matches the block height.
                    if block.last_coinbase_height() != block.height() {
                        bail!("The last coinbase height does not match the block height")
                    }
                } else {
                    // Ensure the block last coinbase target matches the last coinbase target.
                    if block.last_coinbase_target() != self.last_coinbase_target() {
                        bail!("The last coinbase target does not match the coinbase target")
                    }
                    // Ensure the block last coinbase height matches the last coinbase height.
                    if block.last_coinbase_height() != self.last_coinbase_height() {
                        bail!("The last coinbase height does not match the block height")
                    }
                }
            }
            None => {
                // Ensure the last coinbase target matches the previous block coinbase target.
                if block.last_coinbase_target() != self.last_coinbase_target() {
                    bail!("The last coinbase target does not match the previous block coinbase target")
                }
                // Ensure the last coinbase height matches the previous block's last coinbase height.
                if block.last_coinbase_height() != self.last_coinbase_height() {
                    bail!("The last coinbase height does not match the previous block's last coinbase height")
                }
                // Ensure that the cumulative weight is the same as the previous block.
                if block.cumulative_weight() != self.latest_cumulative_weight() {
                    bail!("The cumulative weight does not match the previous block's cumulative weight")
                }
                // Ensure that the cumulative proof target is the same as the previous block.
                if block.cumulative_proof_target() != self.latest_cumulative_proof_target() {
                    bail!("The cumulative proof target does not match the previous cumulative proof target")
                }
            }
        }

        // Construct the next coinbase target.
        let expected_coinbase_target = coinbase_target(
            self.last_coinbase_target(),
            self.last_coinbase_height(),
            block.height(),
            N::ANCHOR_HEIGHT,
            N::NUM_BLOCKS_PER_EPOCH,
            N::GENESIS_COINBASE_TARGET,
        )?;

        // Ensure the coinbase target is correct.
        if block.coinbase_target() != expected_coinbase_target {
            bail!("Invalid coinbase target: expected {expected_coinbase_target}, got {}", block.coinbase_target())
        }

        // Ensure the proof target is correct.
        let expected_proof_target = proof_target(expected_coinbase_target, N::GENESIS_PROOF_TARGET);
        if block.proof_target() != expected_proof_target {
            bail!("Invalid proof target: expected {expected_proof_target}, got {}", block.proof_target())
        }

        /* Block Hash */

        // Compute the Merkle root of the block header.
        let Ok(header_root) = block.header().to_root() else {
            bail!("Failed to compute the Merkle root of the block header");
        };

        // Check the block hash.
        match N::hash_bhp1024(&to_bits_le![block.previous_hash(), header_root]) {
            Ok(candidate_hash) => {
                // Ensure the block hash matches the one in the block.
                if candidate_hash != *block.hash() {
                    bail!("Block {} ({}) has an incorrect block hash.", block.height(), block.hash());
                }
            }
            Err(error) => {
                bail!("Unable to compute block hash for block {} ({}): {error}", block.height(), block.hash())
            }
        };

        /* Authority */

        // Verify the block authority.
        match block.authority() {
            Authority::Beacon(signature) => {
                // Retrieve the signer.
                let signer = signature.to_address();

                // Ensure the block is signed by a validator in the committee.
                if signer != self.genesis_block.authority().to_address() {
                    bail!(
                        "Block {} ({}) is signed by an unauthorized account ({signer})",
                        block.height(),
                        block.hash()
                    );
                }
                // Check the signature.
                if !signature.verify(&signer, &[*block.hash()]) {
                    bail!("Invalid signature for block {} ({})", block.height(), block.hash());
                }
            }
            // TODO: Check the certificates of the quorum.
            Authority::Quorum(_certificates) => {
                // // Ensure the block is signed by a validator in the committee.
                // let signer = block.authority().to_address();
                // if !self.current_committee.read().contains(&signer) {
                //     bail!("Block {} ({}) is signed by an unauthorized account ({signer})", block.height(), block.hash());
                // }
            }
        }

        /* Transactions */

        // Compute the transactions root.
        match block.transactions().to_transactions_root() {
            // Ensure the transactions root matches the one in the block header.
            Ok(root) => {
                if root != block.header().transactions_root() {
                    bail!(
                        "Block {} ({}) has an incorrect transactions root: expected {}",
                        block.height(),
                        block.hash(),
                        block.header().transactions_root()
                    );
                }
            }
            Err(error) => bail!("Failed to compute the Merkle root of the block transactions: {error}"),
        };

        // Ensure the transactions list is not empty.
        if block.transactions().is_empty() {
            bail!("Cannot validate an empty transactions list");
        }

        // Ensure the number of transactions is within the allowed range.
        if block.transactions().len() > Transactions::<N>::MAX_TRANSACTIONS {
            bail!("Cannot validate a block with more than {} transactions", Transactions::<N>::MAX_TRANSACTIONS);
        }

        // FIXME: this intermediate allocation shouldn't be necessary; this is most likely https://github.com/rust-lang/rust/issues/89418.
        let transactions = block.transactions().iter().collect::<Vec<_>>();

        // Ensure each transaction is well-formed and unique.
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
                    fee_transaction.fee_transition().ok_or(anyhow!("Missing the fee"))?,
                ),
                // Reconstruct the unconfirmed execution transaction.
                ConfirmedTransaction::RejectedExecute(_, fee_transaction, rejected) => Transaction::from_execution(
                    rejected.execution().cloned().ok_or(anyhow!("Missing the execution"))?,
                    fee_transaction.fee_transition(),
                ),
            })
            .collect::<Result<Vec<_>>>()?;

        // Ensure the transactions after speculation match.
        if block.transactions() != &self.vm.speculate(state, unconfirmed_transactions.iter())? {
            bail!("The transactions after speculation do not match the transactions in the block");
        }

        /* Finalize Root */

        // Ensure that the block's finalize root matches the transactions.
        let expected_finalize_root = block.transactions().to_finalize_root()?;
        if block.finalize_root() != expected_finalize_root {
            bail!("Invalid finalize root: expected '{expected_finalize_root}', got '{}'", block.finalize_root())
        }

        /* Ratifications Root */

        // Compute the ratifications root of the block.
        let ratifications_root = *N::merkle_tree_bhp::<RATIFICATIONS_DEPTH>(
            &block
                .ratifications()
                .iter()
                .map(|r| Ok::<_, Error>(r.to_bytes_le()?.to_bits_le()))
                .collect::<Result<Vec<_>, _>>()?,
        )?
        .root();
        // Ensure that the block's ratifications root matches the declared ratifications.
        if block.ratifications_root() != ratifications_root {
            bail!("Invalid ratifications root: expected '{ratifications_root}', got '{}'", block.ratifications_root())
        }

        /* Coinbase Proof */

        // Ensure the solutions are valid, if they exist.
        if let Some(coinbase) = block.coinbase() {
            // Ensure the solutions are not accepted after the block height at year 10.
            if block.height() > block_height_at_year(N::BLOCK_TIME, 10) {
                bail!("Coinbase proofs are no longer accepted after the block height at year 10.");
            }
            // Ensure the coinbase accumulator point matches in the block header.
            if block.header().coinbase_accumulator_point() != coinbase.to_accumulator_point()? {
                bail!("Coinbase accumulator point does not match the solutions.");
            }
            // Ensure the number of prover solutions is within the allowed range.
            if coinbase.len() > N::MAX_PROVER_SOLUTIONS {
                bail!("Cannot validate a coinbase proof with more than {} prover solutions", N::MAX_PROVER_SOLUTIONS);
            }
            // Ensure the puzzle commitments are new.
            for puzzle_commitment in coinbase.puzzle_commitments() {
                if self.contains_puzzle_commitment(&puzzle_commitment)? {
                    bail!("Puzzle commitment {puzzle_commitment} already exists in the ledger");
                }
            }
            // Ensure the solutions are valid.
            if !self.coinbase_puzzle.verify(coinbase, &self.latest_epoch_challenge()?, self.latest_proof_target())? {
                bail!("Invalid solutions: {coinbase:?}");
            }
        } else {
            // Ensure that the block header does not contain a coinbase accumulator point.
            if block.header().coinbase_accumulator_point() != Field::<N>::zero() {
                bail!("Coinbase accumulator point should be zero as there are no solutions in the block.");
            }
        }

        Ok(())
    }
}
