// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

use super::*;

impl<N: Network, C: ConsensusStorage<N>> VM<N, C> {
    /// Finalizes the given transactions into the VM.
    /// This method assumes the given transactions **are valid**.
    #[inline]
    pub fn finalize(&self, transactions: &Transactions<N>) -> Result<()> {
        let timer = timer!("VM::finalize");

        // Acquire the write lock on the process.
        let mut process = self.process.write();

        // Initialize a list for the finalize operations.
        let mut finalize_operations = Vec::new();

        // Initialize a list of the accepted transactions.
        let mut accepted = Vec::with_capacity(transactions.len());
        // Initialize a list of the rejected transactions.
        let mut rejected = Vec::with_capacity(transactions.len());

        // Finalize the transactions.
        for transaction in transactions.values() {
            // Process the transaction in an isolated atomic batch.
            // - If the transaction succeeds, the finalize operations are stored.
            // - If the transaction fails, the atomic batch is aborted and no finalize operations are stored.
            let outcome = match transaction {
                // The finalize operation here involves appending the 'stack',
                // and adding the program to the finalize tree.
                Transaction::Deploy(_, _, deployment, _) => process
                    .finalize_deployment::<_, { FinalizeMode::RealRun.to_u8() }>(self.finalize_store(), deployment),
                // The finalize operation here involves calling 'update_key_value',
                // and update the respective leaves of the finalize tree.
                Transaction::Execute(_, execution, _) => process.finalize_execution(self.finalize_store(), execution),
            };
            lap!(timer, "Finalizing transaction {}", transaction.id());

            match outcome {
                // If the transaction succeeded to finalize, continue to the next transaction.
                Ok(operations) => {
                    // Store the finalize operations.
                    finalize_operations.extend(operations);
                    // Store the transaction ID in the accepted list.
                    accepted.push(transaction.id());
                }
                // If the transaction failed to finalize, abort and continue to the next transaction.
                Err(error) => {
                    warn!("Rejected transaction '{}': (in finalize) {error}", transaction.id());
                    // Store the transaction ID and error in the rejected list.
                    rejected.push((transaction.id(), error));
                    // Abort the atomic batch and continue to the next transaction.
                    continue;
                }
            }
        }

        // Ensure all transactions were processed.
        if accepted.len() + rejected.len() != transactions.len() {
            // TODO (howardwu): Identify which transactions in 'transactions' were not processed,
            //  and attempt to process them again (because they came from the block, so we can't remove them now).
            unreachable!("Not all transactions were processed");
        }

        finish!(timer);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_utilities::TestRng;

    #[test]
    fn test_finalize() {
        let rng = &mut TestRng::default();

        let vm = crate::vm::test_helpers::sample_vm();

        // Fetch a deployment transaction.
        let deployment_transaction = crate::vm::test_helpers::sample_deployment_transaction(rng);

        // Finalize the transaction.
        vm.finalize(&Transactions::from(&[deployment_transaction.clone()])).unwrap();

        // Ensure the VM can't redeploy the same transaction.
        assert!(vm.finalize(&Transactions::from(&[deployment_transaction])).is_err());
    }
}
