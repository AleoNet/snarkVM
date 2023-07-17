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
    /// Checks the given transaction is well-formed and unique.
    pub fn check_transaction_basic(&self, transaction: &Transaction<N>, rejected_id: Option<Field<N>>) -> Result<()> {
        let transaction_id = transaction.id();

        // Ensure the ledger does not already contain the given transaction ID.
        if self.contains_transaction_id(&transaction_id)? {
            bail!("Transaction '{transaction_id}' already exists in the ledger")
        }

        // Ensure the ledger does not already contain the given transition ID.
        for transition_id in transaction.transition_ids() {
            if self.contains_transition_id(transition_id)? {
                bail!("Transition ID '{transition_id}' already exists in the ledger")
            }
        }

        // Ensure the mint transaction is attributed to a validator in the committee.
        if transaction.is_mint() {
            // Retrieve the execution.
            let Some(execution) = transaction.execution() else {
                bail!("Invalid mint transaction: expected an execution");
            };
            // Loop over the mint transitions and ensure the address is authorized.
            for transition in execution.transitions().filter(|t| t.is_mint()) {
                // Retrieve the address that minted.
                let address = mint_address(transition)?;
                // Check if the address is in the current committee.
                if !self.current_committee.read().contains(address) {
                    bail!("Mint transaction ({transaction_id}) is from an unauthorized account ({address})")
                }
            }
        }

        /* Fee */

        // TODO (raychu86): Remove the split check when batch executions are integrated.
        let can_skip_fee = match transaction.execution() {
            Some(execution) => (transaction.is_mint() || transaction.is_split()) && execution.len() == 1,
            None => false,
        };

        if !can_skip_fee {
            // Retrieve the transaction fee.
            let fee = *transaction.fee()?;
            // Retrieve the minimum cost of the transaction.
            let (cost, _) = match transaction {
                // Compute the deployment cost.
                Transaction::Deploy(_, _, deployment, _) => synthesizer::deployment_cost(deployment)?,
                // Compute the execution cost.
                Transaction::Execute(_, execution, _) => synthesizer::execution_cost(self.vm(), execution)?,
                // TODO (howardwu): Plug in the Rejected struct, to compute the cost.
                Transaction::Fee(_, _) => (0, (0, 0)),
            };
            // Ensure the transaction has a sufficient fee.
            if cost > fee {
                bail!("Transaction '{transaction_id}' has an insufficient fee - expected at least {cost} microcredits")
            }
        }

        /* Proof */

        // Ensure the transaction is valid.
        self.vm().check_transaction(transaction, rejected_id)?;

        /* Program */

        // If the transaction is a deployment, then perform deployment checks.
        if let Transaction::Deploy(_, _, deployment, _) = &transaction {
            // Ensure the edition is correct.
            if deployment.edition() != N::EDITION {
                bail!("Invalid program deployment: expected edition {}", N::EDITION)
            }
            // Ensure the program ID is not already in the ledger.
            if self.contains_program_id(deployment.program_id())? {
                bail!("Program ID '{}' already exists in the ledger", deployment.program_id())
            }
        }

        /* Input */

        // Ensure the ledger does not already contain the given input ID.
        for input_id in transaction.input_ids() {
            if self.contains_input_id(input_id)? {
                bail!("Input ID '{input_id}' already exists in the ledger")
            }
        }

        // Ensure the ledger does not already contain a given serial numbers.
        for serial_number in transaction.serial_numbers() {
            if self.contains_serial_number(serial_number)? {
                bail!("Serial number '{serial_number}' already exists in the ledger")
            }
        }

        // Ensure the ledger does not already contain a given tag.
        for tag in transaction.tags() {
            if self.contains_tag(tag)? {
                bail!("Tag '{tag}' already exists in the ledger")
            }
        }

        /* Output */

        // Ensure the ledger does not already contain the given output ID.
        for output_id in transaction.output_ids() {
            if self.contains_output_id(output_id)? {
                bail!("Output ID '{output_id}' already exists in the ledger")
            }
        }

        // Ensure the ledger does not already contain a given commitments.
        for commitment in transaction.commitments() {
            if self.contains_commitment(commitment)? {
                bail!("Commitment '{commitment}' already exists in the ledger")
            }
        }

        // Ensure the ledger does not already contain a given nonces.
        for nonce in transaction.nonces() {
            if self.contains_nonce(nonce)? {
                bail!("Nonce '{nonce}' already exists in the ledger")
            }
        }

        /* Metadata */

        // Ensure the ledger does not already contain a given transition public keys.
        for tpk in transaction.transition_public_keys() {
            if self.contains_tpk(tpk)? {
                bail!("Transition public key '{tpk}' already exists in the ledger")
            }
        }

        // Ensure the ledger does not already contain a given transition commitment.
        for tcm in transaction.transition_commitments() {
            if self.contains_tcm(tcm)? {
                bail!("Transition commitment '{tcm}' already exists in the ledger")
            }
        }

        Ok(())
    }

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

        // Ensure the next round is correct.
        if self.latest_round() > 0 {
            bail!("The next block has an incorrect round number")
        }

        // TODO (raychu86): Ensure the next block timestamp is the median of proposed blocks.
        // Ensure the next block timestamp is after the current block timestamp.
        if block.height() > 0 {
            let next_timestamp = block.header().timestamp();
            let latest_timestamp = self.latest_block().header().timestamp();
            if next_timestamp <= latest_timestamp {
                bail!("The next block timestamp {next_timestamp} is before the current timestamp {latest_timestamp}")
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

        // If the block is the genesis block, check that it is valid.
        if block.height() == 0 && !block.is_genesis() {
            bail!("Invalid genesis block");
        }

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
        if block.height() > 0 {
            match block.coinbase() {
                Some(coinbase) => {
                    // Ensure the last coinbase target matches the coinbase target.
                    if block.last_coinbase_target() != block.coinbase_target() {
                        bail!("The last coinbase target does not match the coinbase target")
                    }
                    // Ensure the last coinbase timestamp matches the block timestamp.
                    if block.last_coinbase_timestamp() != block.timestamp() {
                        bail!("The last coinbase timestamp does not match the block timestamp")
                    }
                    // Compute the combined proof target.
                    let combined_proof_target = coinbase.to_combined_proof_target()?;
                    // Ensure that the cumulative weight includes the next block's combined proof target.
                    if block.cumulative_weight()
                        != self.latest_cumulative_weight().saturating_add(combined_proof_target)
                    {
                        bail!("The cumulative weight does not include the block combined proof target")
                    }
                    // Ensure that the block combined proof target matches the coinbase combined proof target.
                    if block.combined_proof_target() != combined_proof_target {
                        bail!("The blocks combined proof target does not match the coinbase combined proof target")
                    }
                    // Compute the expected accumulated proof target.
                    let accumulated_proof_target =
                        self.latest_accumulated_proof_target().saturating_add(combined_proof_target);
                    let expected_accumulated_proof_target =
                        match accumulated_proof_target >= u128::try_from(self.latest_coinbase_target())? {
                            true => 0u128,
                            false => accumulated_proof_target.saturating_sub(combined_proof_target),
                        };
                    // Ensure that the accumulated proof target is correct.
                    if block.accumulated_proof_target() != expected_accumulated_proof_target {
                        bail!("The accumulated proof target does not match the expected accumulated proof target")
                    }
                }
                None => {
                    // Ensure the last coinbase target matches the previous block coinbase target.
                    if block.last_coinbase_target() != self.last_coinbase_target() {
                        bail!("The last coinbase target does not match the previous block coinbase target")
                    }
                    // Ensure the last coinbase timestamp matches the previous block's last coinbase timestamp.
                    if block.last_coinbase_timestamp() != self.last_coinbase_timestamp() {
                        bail!("The last coinbase timestamp does not match the previous block's last coinbase timestamp")
                    }
                    // Ensure that the cumulative weight is the same as the previous block.
                    if block.cumulative_weight() != self.latest_cumulative_weight() {
                        bail!("The cumulative weight does not match the previous block's cumulative weight")
                    }
                    // Ensure that the block combined proof target is zero.
                    if block.combined_proof_target() != 0 {
                        bail!("The combined proof target is not zero")
                    }
                    // Ensure that the accumulated proof target is the same as the previous block.
                    if block.accumulated_proof_target() != self.latest_accumulated_proof_target() {
                        bail!(
                            "The accumulated proof target does not match the previous block's accumulated proof target"
                        )
                    }
                }
            }
        }

        // Construct the next coinbase target.
        let expected_coinbase_target = coinbase_target(
            self.last_coinbase_target(),
            self.last_coinbase_timestamp(),
            block.timestamp(),
            N::ANCHOR_TIME,
            N::NUM_BLOCKS_PER_EPOCH,
            N::GENESIS_COINBASE_TARGET,
        )?;

        if block.coinbase_target() != expected_coinbase_target {
            bail!("Invalid coinbase target: expected {}, got {}", expected_coinbase_target, block.coinbase_target())
        }

        // Ensure the proof target is correct.
        let expected_proof_target = proof_target(expected_coinbase_target, N::GENESIS_PROOF_TARGET);
        if block.proof_target() != expected_proof_target {
            bail!("Invalid proof target: expected {}, got {}", expected_proof_target, block.proof_target())
        }

        /* Block Hash */

        // Compute the Merkle root of the block header.
        let header_root = match block.header().to_root() {
            Ok(root) => root,
            Err(error) => bail!("Failed to compute the Merkle root of the block header: {error}"),
        };

        // Check the block hash.
        match N::hash_bhp1024(&[block.previous_hash().to_bits_le(), header_root.to_bits_le()].concat()) {
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

        /* Signature */

        // Ensure the block is signed by a validator in the committee
        let signer = block.signature().to_address();
        if !self.current_committee.read().contains(&signer) {
            bail!("Block {} ({}) is signed by an unauthorized account ({signer})", block.height(), block.hash());
        }

        // Check the signature.
        if !block.signature().verify(&signer, &[*block.hash()]) {
            bail!("Invalid signature for block {} ({})", block.height(), block.hash());
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

            self.check_transaction_basic(transaction.deref(), rejected_id)
                .map_err(|e| anyhow!("Invalid transaction found in the transactions list: {e}"))
        })?;

        // Construct the finalize state.
        let state = FinalizeGlobalState::new::<N>(
            block.round(),
            block.height(),
            block.cumulative_weight(),
            block.combined_proof_target(),
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

        // Ensure the coinbase solution is valid, if it exists.
        if let Some(coinbase) = block.coinbase() {
            // Ensure coinbase solutions are not accepted after the anchor block height at year 10.
            if block.height() > anchor_block_height(N::ANCHOR_TIME, 10) {
                bail!("Coinbase proofs are no longer accepted after the anchor block height at year 10.");
            }
            // Ensure the coinbase accumulator point matches in the block header.
            if block.header().coinbase_accumulator_point() != coinbase.to_accumulator_point()? {
                bail!("Coinbase accumulator point does not match the coinbase solution.");
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
            // Ensure the coinbase solution is valid.
            if !self.coinbase_puzzle.verify(
                coinbase,
                &self.latest_epoch_challenge()?,
                self.latest_coinbase_target(),
                self.latest_proof_target(),
            )? {
                bail!("Invalid coinbase solution: {:?}", coinbase);
            }
        } else {
            // Ensure that the block header does not contain a coinbase accumulator point.
            if block.header().coinbase_accumulator_point() != Field::<N>::zero() {
                bail!("Coinbase accumulator point should be zero as there is no coinbase solution in the block.");
            }
        }

        Ok(())
    }
}

impl<N: Network, C: ConsensusStorage<N>> Ledger<N, C> {
    // TODO (raychu86): Integrate subdag/certificates into block.
    /// Checks the given block is valid next block.
    pub fn check_next_block_bft(
        &self,
        block: &Block<N>,
        committed_subdag: BTreeMap<u64, Vec<BatchCertificate<N>>>,
    ) -> Result<()> {
        // Perform the non-bft checks.
        self.check_next_block(block)?;

        // Retrieve the leader certificate in the round.
        let leader_certificate = match committed_subdag.iter().next_back() {
            Some((_, value)) => {
                ensure!(value.len() == 1, "There should only be one leader certificate per round");
                value[0].clone()
            }
            None => bail!("Missing leader certificate"),
        };

        // Check that the block timestamp is the median timestamp of the leader certificate.
        ensure!(
            block.timestamp() == leader_certificate.median_timestamp(),
            "Block timestamp does not match the median timestamp of the leader certificate"
        );

        // Check that the round number is correct.
        ensure!(
            block.round() == leader_certificate.round(),
            "The block round number is incorrect ({} != {})",
            block.round(),
            leader_certificate.round()
        );

        // Check that the subdag is valid.
        // All `previous_certificate_ids` in the parent should be in the subdag. Except the bottom layer, whose `previous_certificate_ids` should already exist in the ledger.
        let mut previous_certificates_to_check = leader_certificate.previous_certificate_ids().clone();
        let mut round_to_check = leader_certificate.round().saturating_sub(1);

        while !previous_certificates_to_check.is_empty() {
            match committed_subdag.get(&round_to_check) {
                Some(subdag_certificates) => {
                    // Construct the new certificates to check.
                    let mut new_previous_certificates_to_check = IndexSet::new();

                    // Track the certificates to check.
                    let mut certificates_index = 0;

                    // TODO (raychu86): Is this ordering correct?
                    // Check that the certificates correspond to the `previous_certificates` in the parent.
                    for expected_certificate_id in previous_certificates_to_check.iter() {
                        // Check if the certificate already exists in the ledger.
                        // TODO (raychu86): The functionality currently only exists in `LedgerService` in snarkOS.
                        // if self.contains_certificate(&expected_certificate_id) {
                        //     continue;
                        // }

                        // Get the certificate at the given index.
                        let certificate =
                            subdag_certificates.get(certificates_index).ok_or(anyhow!("Missing certificate"))?;
                        ensure!(
                            certificate.certificate_id() == *expected_certificate_id,
                            "Certificate does not match the expected certificate id"
                        );

                        // Check that the certificate round is correct.
                        ensure!(
                            certificate.round() == round_to_check,
                            "Certificate round does not match the expected round"
                        );

                        // Increment the certificates.
                        certificates_index += 1;
                        // Add the new previous certificates to check.
                        new_previous_certificates_to_check.extend(certificate.previous_certificate_ids().clone());
                    }

                    // Update the certificates to check.
                    previous_certificates_to_check = new_previous_certificates_to_check;
                    round_to_check = round_to_check.saturating_sub(1);
                }
                None => {
                    // Missing the previous round in the committed subdag.
                    // Check that each certificate already exists in the ledger.
                    for certificate_id in previous_certificates_to_check.iter() {
                        // TODO (raychu86): The functionality currently only exists in `LedgerService` in snarkOS.
                        // ensure!(self.contains_certificate(certificate_id)?, "Missing certificate in the ledger");
                    }
                }
            }
        }

        // Ensure that the last committed certificate round of the subdag is equivalent to the final `round_to_check`.
        if !block.is_genesis() {
            // Get the smallest round in the committed subdag.
            match committed_subdag.keys().next() {
                Some(round) => ensure!(
                    *round == round_to_check,
                    "The last committed certificate round of the ledger is not the bottom level of the committed subdag"
                ),
                None => bail!("Missing last committed certificate round of the ledger"),
            }
        }

        // Flatten the transmission ids from the subdag into a single vector.
        let transmission_ids: IndexSet<TransmissionID<N>> = {
            // TODO (raychu86): Add helper methods for the following logic. Currently copied from `narwhal` branch in snarkOS.
            // Initialize a map for the deduped transmissions.
            let mut transmission_ids = IndexSet::new();
            // Start from the oldest leader certificate.
            for certificate in committed_subdag.values().flatten() {
                // Retrieve the transmissions.
                for transmission_id in certificate.transmission_ids() {
                    // If the transmission already exists in the map, skip it.
                    if transmission_ids.contains(transmission_id) {
                        continue;
                    }
                    // If the transmission already exists in the ledger, skip it.
                    // Note: On failure to read from the ledger, we skip including this transmission, out of safety.
                    if self.contains_transmission(transmission_id).unwrap_or(true) {
                        continue;
                    }
                    // Add the transmission to the set.
                    transmission_ids.insert(*transmission_id);
                }
            }

            transmission_ids
        };

        // Add checks that the subdag construction corresponds to the block transactions properly.
        // Fetch the transactions iterator.
        let mut transaction_ids = block.transactions().transaction_ids();
        // Fetch the ratifications iterator.
        let mut ratifications_ids = block.ratifications();
        // Fetch the additional solutions from the transmission ids.
        let mut solutions =
            block.coinbase().map(|coinbase| coinbase.partial_solutions().iter()).unwrap_or_else(|| [].iter());

        // Iterate through the provided transmission ids and ensure that the `Transmissions` ordering is correct.
        for transmission_id in transmission_ids {
            match transmission_id {
                // Check the next ratification ID matches the expected ID.
                TransmissionID::Ratification => {
                    // ensure!(ratifications.next() == Some(expected_id), "Transaction ordering does not match.")
                }
                // Check the next solution matches the expected commitment.
                TransmissionID::Solution(commitment) => {
                    ensure!(
                        solutions.next().map(|solution| solution.commitment()) == Some(commitment),
                        "Solution ordering does not match."
                    )
                }
                // Check the next transaction ID matches the expected ID.
                TransmissionID::Transaction(expected_id) => {
                    ensure!(transaction_ids.next() == Some(&expected_id), "Transaction ordering does not match.")
                }
            }
        }

        // Ensure that there are no more transactions in the block.
        ensure!(transaction_ids.next().is_none(), "There exists more transactions than expected.");
        // Ensure that there are no more solutions in the block.
        ensure!(solutions.next().is_none(), "There exists more solutions than expected.");

        // Compute the combined proof target of the prover solutions as a u128.
        let combined_proof_target =
            block.coinbase().map(|coinbase| coinbase.to_combined_proof_target()).unwrap_or(Ok(0))?;

        // Check that the remaining ratification ids correspond to the prover/validator rewards.
        let (proving_rewards, staking_rewards) = match block.coinbase().map(|coinbase| coinbase.partial_solutions()) {
            Some(partial_solutions) => {
                // Calculate the coinbase reward.
                let coinbase_reward = coinbase_reward(
                    self.last_coinbase_timestamp(),
                    block.timestamp(),
                    block.height(),
                    N::STARTING_SUPPLY,
                    N::ANCHOR_TIME,
                )?;

                // Calculate the proving rewards.
                let proving_rewards = proving_rewards(
                    partial_solutions,
                    coinbase_reward,
                    combined_proof_target,
                    self.latest_accumulated_proof_target(),
                    self.latest_coinbase_target(),
                )?;
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

        // Ensure that the remaining ratifications is equivalent to [proving_rewards, staking_rewards].
        let expected_remaining_ratifications = [proving_rewards, staking_rewards].concat();
        ensure!(
            ratifications_ids == &expected_remaining_ratifications,
            "Block ratifications do not match the expected rewards."
        );

        Ok(())
    }
}
