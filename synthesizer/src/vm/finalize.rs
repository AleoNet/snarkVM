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
    pub fn finalize(&self, transactions: &Transactions<N>, speculate: Option<Speculate<N>>) -> Result<()> {
        let timer = timer!("VM::finalize");

        // Initialize a new speculate struct if one was not provided.
        let speculate = match speculate {
            Some(speculate) => speculate,
            None => {
                // Perform the transaction speculation.
                let mut speculate = Speculate::new(self.finalize_store().current_storage_root());
                speculate.speculate_transactions(self, &transactions.iter().cloned().collect::<Vec<_>>())?;

                speculate
            }
        };

        // Ensure the transactions match the speculate transactions.
        if transactions.transaction_ids().copied().collect::<Vec<_>>() != speculate.accepted_transactions() {
            return Err(anyhow!("Speculate transactions do not match block transactions transactions"));
        }

        // Finalize the transactions.
        atomic_write_batch!(self, {
            // Acquire the write lock on the process.
            let mut process = self.process.write();

            // Update the storage tree.
            if !speculate.operations.is_empty() {
                // Construct the new storage tree.
                let new_storage_tree = match speculate.commit(self) {
                    Ok(new_storage_tree) => new_storage_tree,
                    Err(err) => {
                        // If the commit failed, set the speculate flag to `false`.
                        self.finalize_store().is_speculate.store(false, Ordering::SeqCst);

                        bail!("Failed to commit speculate: {err}")
                    }
                };

                // Acquire the write lock on the tree.
                let mut storage_tree = self.finalize_store().tree.write();

                // Update the storage tree.
                *storage_tree = new_storage_tree;
            }

            // Update the `is_speculate` flag.
            self.finalize_store().is_speculate.store(true, Ordering::SeqCst);

            // TODO (raychu86): Use the `Speculate` struct to finalize the transactions. This will
            //  reduce the re-execution of the transactions.
            for transaction in transactions.values() {
                // Finalize the transaction.
                match transaction {
                    Transaction::Deploy(_, _, deployment, _) => {
                        if let Err(err) = process.finalize_deployment(self.finalize_store(), deployment) {
                            // If the commit failed, set the speculate flag to `false`.
                            self.finalize_store().is_speculate.store(false, Ordering::SeqCst);

                            bail!("Failed to finalize deployment: {err}")
                        }
                        lap!(timer, "Finalize deployment");
                    }
                    Transaction::Execute(_, execution, _) => {
                        if let Err(err) = process.finalize_execution(self.finalize_store(), execution) {
                            // If the commit failed, set the speculate flag to `false`.
                            self.finalize_store().is_speculate.store(false, Ordering::SeqCst);

                            bail!("Failed to finalize execution: {err}")
                        }
                        lap!(timer, "Finalize execution");
                    }
                }
            }

            self.finalize_store().is_speculate.store(false, Ordering::SeqCst);

            Ok(())
        });

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
        vm.finalize(&Transactions::from(&[deployment_transaction.clone()]), None).unwrap();

        // Ensure the VM can't redeploy the same transaction.
        assert!(vm.finalize(&Transactions::from(&[deployment_transaction]), None).is_err());
    }
}
