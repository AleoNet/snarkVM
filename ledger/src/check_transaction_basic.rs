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
}
