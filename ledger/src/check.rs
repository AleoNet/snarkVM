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
}
