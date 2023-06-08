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

        // TODO (raychu86): Remove this once proper coinbase transactions are integrated with consensus.
        // Ensure the coinbase transaction is attributed to a validator in the committee.
        if transaction.is_coinbase() {
            if let Transaction::Execute(id, execution, _) = transaction {
                // Loop over coinbase transitions and check the input address.
                for transition in execution.transitions().filter(|t| t.is_coinbase()) {
                    // Get the input address of the coinbase transition.
                    match transition.inputs().get(0) {
                        Some(Input::Public(_, Some(Plaintext::Literal(Literal::Address(address), _)))) => {
                            // Check if the address is in the current committee.
                            if !self.current_committee.read().contains(address) {
                                bail!("Coinbase transaction ({id}) is from an unauthorized account ({address})",);
                            }
                        }
                        _ => bail!("Invalid coinbase transaction: Missing public input in 'credits.aleo/mint'"),
                    }
                }
            } else {
                bail!("Invalid coinbase transaction");
            }
        }

        /* Fee */

        // TODO (raychu86): TODO (raychu86): Consider fees for `finalize` execution when it is ready.
        // Ensure the transaction has a sufficient fee.
        let fee = transaction.fee()?;
        match transaction {
            Transaction::Deploy(_, _, deployment, _) => {
                // Check that the fee in microcredits is at least the deployment size in bytes.
                if deployment.size_in_bytes()?.saturating_mul(N::DEPLOYMENT_FEE_MULTIPLIER) > *fee {
                    bail!("Transaction '{transaction_id}' has insufficient fee to cover its storage in bytes")
                }
            }
            Transaction::Execute(_, execution, _) => {
                // TODO (raychu86): Remove the split check when batch executions are integrated.
                // If the transaction is not a coinbase or split transaction, check that the fee in microcredits is at least the execution size in bytes.
                if !((transaction.is_coinbase() || transaction.is_split()) && execution.len() == 1)
                    && execution.size_in_bytes()? > *fee
                {
                    bail!("Transaction '{transaction_id}' has insufficient fee to cover its storage in bytes")
                }
            }
            // TODO (howardwu): Pass the confirmed transaction in and check its rejected size against the fee.
            Transaction::Fee(..) => (),
        }

        /* Proof(s) */

        // Ensure the transaction is valid.
        self.vm().check_transaction(transaction, rejected_id)?;

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

        /* Program */

        // Ensure that the ledger does not already contain the given program ID.
        if let Transaction::Deploy(_, _, deployment, _) = &transaction {
            let program_id = deployment.program_id();
            if self.contains_program_id(program_id)? {
                bail!("Program ID '{program_id}' already exists in the ledger")
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

        // TODO (raychu86): Ensure the next round number includes timeouts.
        // Ensure the next round is correct.
        if self.latest_round() > 0 && self.latest_round() + 1 /*+ block.number_of_timeouts()*/ != block.round() {
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

        for transaction_id in block.transaction_ids() {
            // Ensure the transaction in the block do not already exist.
            if self.contains_transaction_id(transaction_id)? {
                bail!("Transaction '{transaction_id}' already exists in the ledger")
            }
        }

        /* Input */

        // Ensure the ledger does not already contain a given serial numbers.
        for serial_number in block.serial_numbers() {
            if self.contains_serial_number(serial_number)? {
                bail!("Serial number '{serial_number}' already exists in the ledger")
            }
        }

        /* Output */

        // Ensure the ledger does not already contain a given commitments.
        for commitment in block.commitments() {
            if self.contains_commitment(commitment)? {
                bail!("Commitment '{commitment}' already exists in the ledger")
            }
        }

        // Ensure the ledger does not already contain a given nonces.
        for nonce in block.nonces() {
            if self.contains_nonce(nonce)? {
                bail!("Nonce '{nonce}' already exists in the ledger")
            }
        }

        /* Metadata */

        // Ensure the ledger does not already contain a given transition public keys.
        for tpk in block.transition_public_keys() {
            if self.contains_tpk(tpk)? {
                bail!("Transition public key '{tpk}' already exists in the ledger")
            }
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

        // TODO (raychu86): Include mints from the leader of each round.
        // TODO (raychu86): Clean this up or create a `total_supply_delta` in `Transactions`.
        // Calculate the new total supply of microcredits after the block.
        let mut new_total_supply_in_microcredits = self.latest_total_supply_in_microcredits();
        for confirmed_tx in block.transactions().iter() {
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

        // Ensure the total supply in microcredits is correct.
        if new_total_supply_in_microcredits != block.total_supply_in_microcredits() {
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
                    // Ensure that the cumulative weight includes the next block's cumulative proof target.
                    if block.cumulative_weight()
                        != self.latest_cumulative_weight().saturating_add(coinbase.to_cumulative_proof_target()?)
                    {
                        bail!("The cumulative weight does not include the block cumulative proof target")
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

        // Ensure each transaction is well-formed and unique.
        cfg_iter!(block.transactions()).try_for_each(|transaction| {
            // Construct the rejected ID.
            let rejected_id = match transaction {
                ConfirmedTransaction::AcceptedDeploy(..) | ConfirmedTransaction::AcceptedExecute(..) => None,
                ConfirmedTransaction::RejectedDeploy(_, _, deployment) => Some(deployment.to_deployment_id()?),
                ConfirmedTransaction::RejectedExecute(_, _, execution) => Some(execution.to_execution_id()?),
            };

            self.check_transaction_basic(transaction, rejected_id)
                .map_err(|e| anyhow!("Invalid transaction found in the transactions list: {e}"))
        })?;

        // Ensure the transactions after speculation match.
        if block.transactions() != &self.vm.speculate(block.transactions().iter().map(|tx| tx.deref()))? {
            bail!("The transactions after speculation do not match the transactions in the block");
        }

        /* Finalize Root */

        // Ensure that the block's finalize root matches the transactions.
        let expected_finalize_root = block.transactions().to_finalize_root()?;
        if block.finalize_root() != expected_finalize_root {
            bail!("Invalid finalize root: expected '{expected_finalize_root}', got '{}'", block.finalize_root())
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
