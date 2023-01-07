// Copyright (C) 2019-2022 Aleo Systems Inc.
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
        atomic_write_batch!(self, {
            // Acquire the write lock on the process.
            let mut process = self.process.write();

            for transaction in transactions.values() {
                // Finalize the transaction.
                match transaction {
                    Transaction::Deploy(_, deployment, _) => {
                        process.finalize_deployment(self.program_store(), deployment)?;
                        lap!(timer, "Finalize deployment");
                    }
                    Transaction::Execute(_, execution, _) => {
                        process.finalize_execution(self.program_store(), execution)?;
                        lap!(timer, "Finalize execution");
                    }
                }
            }
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
        vm.finalize(&Transactions::from(&[deployment_transaction.clone()])).unwrap();

        // Ensure the VM can't redeploy the same transaction.
        assert!(vm.finalize(&Transactions::from(&[deployment_transaction])).is_err());
    }
}
