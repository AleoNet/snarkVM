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

        // TODO (howardwu): DEPRECATE THIS - Remove support for `mint` altogether.
        // Ensure the mint transaction is attributed to a validator in the committee.
        if transaction.contains_mint() {
            // Retrieve the execution.
            let Some(execution) = transaction.execution() else {
                bail!("Invalid mint transaction: expected an execution");
            };
            // Loop over the mint transitions and ensure the address is authorized.
            for transition in execution.transitions().filter(|t| t.is_mint()) {
                // Retrieve the address that minted.
                let address = mint_address(transition)?;
                // Check if the address is in the current committee.
                if *address != self.genesis_block.authority().to_address() {
                    bail!("Mint transaction ({transaction_id}) is from an unauthorized account ({address})")
                }
            }
        }

        /* Fee */

        // If the transaction contains only 1 transition, and the transition is a split, then the fee can be skipped.
        // TODO (howardwu): Remove support for 'mint'.
        let can_skip_fee = match transaction.execution() {
            Some(execution) => (transaction.contains_mint() || transaction.contains_split()) && execution.len() == 1,
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

        /* Transaction */

        // Ensure the transaction is valid.
        self.vm().check_transaction(transaction, rejected_id)?;

        Ok(())
    }
}
