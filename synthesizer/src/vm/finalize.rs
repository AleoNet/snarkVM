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
    /// Finalizes the given transactions into the VM,
    /// returning the list of accepted transaction IDs, rejected transaction IDs, and finalize operations.
    #[inline]
    pub fn finalize<const FINALIZE_MODE: u8>(
        &self,
        transactions: &Transactions<N>,
    ) -> Result<(Vec<N::TransactionID>, Vec<N::TransactionID>, Vec<FinalizeOperation<N>>)> {
        let timer = timer!("VM::finalize");

        // Initialize a list for the deployed stacks.
        let stacks = Arc::new(Mutex::new(Vec::new()));
        // Initialize a list for the finalize operations.
        let finalize_operations = Arc::new(Mutex::new(Vec::new()));

        // Initialize a list of the accepted transactions.
        let accepted = Arc::new(Mutex::new(Vec::with_capacity(transactions.len())));
        // Initialize a list of the rejected transactions.
        let rejected = Arc::new(Mutex::new(Vec::with_capacity(transactions.len())));

        atomic_write_batch!(self.finalize_store(), {
            // Acquire the write lock on the process.
            // Note: Due to the highly-sensitive nature of processing all `finalize` calls,
            // we choose to acquire the write lock for the entire duration of this atomic batch.
            let mut process = self.process.write();

            // Finalize the transactions.
            for transaction in transactions.values() {
                // Process the transaction in an isolated atomic batch.
                // - If the transaction succeeds, the finalize operations are stored.
                // - If the transaction fails, the atomic batch is aborted and no finalize operations are stored.
                let outcome = match transaction {
                    // The finalize operation here involves appending the 'stack',
                    // and adding the program to the finalize tree.
                    Transaction::Deploy(_, _, deployment, _) => {
                        process.finalize_deployment(self.finalize_store(), deployment).map(|(stack, operations)| {
                            // Store the stack.
                            stacks.lock().push(stack);
                            // Return the finalize operations.
                            operations
                        })
                    }
                    // The finalize operation here involves calling 'update_key_value',
                    // and update the respective leaves of the finalize tree.
                    Transaction::Execute(_, execution, _) => {
                        process.finalize_execution(self.finalize_store(), execution)
                    }
                };
                lap!(timer, "Finalizing transaction {}", transaction.id());

                match outcome {
                    // If the transaction succeeded to finalize, continue to the next transaction.
                    Ok(operations) => {
                        // Store the finalize operations.
                        finalize_operations.lock().extend(operations);
                        // Store the transaction ID in the accepted list.
                        accepted.lock().push(transaction.id());
                    }
                    // If the transaction failed to finalize, abort and continue to the next transaction.
                    Err(error) => {
                        warn!("Rejected transaction '{}': (in finalize) {error}", transaction.id());
                        // Store the transaction ID in the rejected list.
                        rejected.lock().push(transaction.id());
                        // Abort the atomic batch and continue to the next transaction.
                        continue;
                    }
                }
            }

            // Handle the atomic batch, based on the finalize mode.
            match FinalizeMode::from_u8(FINALIZE_MODE)? {
                // If this is a real run, commit the atomic batch.
                FinalizeMode::RealRun => {
                    // Commit the deployed stacks.
                    for stack in stacks.lock().drain(..) {
                        // Add the stack to the process.
                        process.add_stack(stack);
                    }
                    Ok(())
                }
                // If this is a dry run, abort the atomic batch.
                FinalizeMode::DryRun => bail!("Dry run of finalize"),
            }
        });

        // Retrieve the accepted transactions, rejected transactions, and finalize operations.
        let accepted = accepted.lock().clone();
        let rejected = rejected.lock().clone();
        let finalize_operations = finalize_operations.lock().clone();

        // Ensure all transactions were processed.
        if accepted.len() + rejected.len() != transactions.len() {
            // TODO (howardwu): Identify which transactions in 'transactions' were not processed,
            //  and attempt to process them again (because they came from the block, so we can't remove them now).
            unreachable!("Not all transactions were processed");
        }

        finish!(timer);

        Ok((accepted, rejected, finalize_operations))
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
        vm.finalize::<{ FinalizeMode::RealRun.to_u8() }>(&Transactions::from(&[deployment_transaction.clone()]))
            .unwrap();

        // Ensure the VM can't redeploy the same transaction.
        assert!(
            vm.finalize::<{ FinalizeMode::RealRun.to_u8() }>(&Transactions::from(&[deployment_transaction])).is_err()
        );
    }
}
