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

use crate::{
    atomic_batch_scope,
    block::RollbackOperation,
    cow_to_cloned,
    store::helpers::{Map, MapRead},
};
use console::network::prelude::*;

use anyhow::Result;
use core::marker::PhantomData;

/// A trait for state rollback storage.
pub trait RollbackStorage<N: Network>: 'static + Clone + Send + Sync {
    /// The mapping of `transaction id` to `[rollback operation]`.
    type RollbackMap: for<'a> Map<'a, N::TransactionID, Vec<RollbackOperation<N>>>;

    /// Initializes the program state storage.
    fn open(dev: Option<u16>) -> Result<Self>;

    /// Returns the rollback map.
    fn rollback_map(&self) -> &Self::RollbackMap;

    /// Returns the optional development ID.
    fn dev(&self) -> Option<u16>;

    /// Starts an atomic batch write operation.
    fn start_atomic(&self) {
        self.rollback_map().start_atomic();
    }

    /// Checks if an atomic batch is in progress.
    fn is_atomic_in_progress(&self) -> bool {
        self.rollback_map().is_atomic_in_progress()
    }

    /// Checkpoints the atomic batch.
    fn atomic_checkpoint(&self) {
        self.rollback_map().atomic_checkpoint();
    }

    /// Clears the latest atomic batch checkpoint.
    fn clear_latest_checkpoint(&self) {
        self.rollback_map().clear_latest_checkpoint();
    }

    /// Rewinds the atomic batch to the previous checkpoint.
    fn atomic_rewind(&self) {
        self.rollback_map().atomic_rewind();
    }

    /// Aborts an atomic batch write operation.
    fn abort_atomic(&self) {
        self.rollback_map().abort_atomic();
    }

    /// Finishes an atomic batch write operation.
    fn finish_atomic(&self) -> Result<()> {
        self.rollback_map().finish_atomic()
    }

    /// Inserts the rollback operations for the given `transaction ID` into storage.
    fn insert_rollback_operations(
        &self,
        transaction_id: &N::TransactionID,
        rollback_operations: Vec<RollbackOperation<N>>,
    ) -> Result<()> {
        // Ensure the transaction ID does not already exist.
        if self.rollback_map().contains_key_speculative(transaction_id)? {
            bail!(
                "Illegal operation: transaction ID '{transaction_id}' already exists in storage - cannot insert again."
            )
        }

        // Insert the rollback operations into storage.
        atomic_batch_scope!(self, {
            self.rollback_map().insert(*transaction_id, rollback_operations)?;

            Ok(())
        })
    }

    /// Removes the rollback operations for the given transaction ID.
    fn remove_rollback_operations(&self, transaction_id: &N::TransactionID) -> Result<()> {
        atomic_batch_scope!(self, {
            self.rollback_map().remove(transaction_id)?;

            Ok(())
        })
    }

    /// Returns `true` if the given `transaction ID` exist.
    fn contains_transaction_id_confirmed(&self, transaction_id: &N::TransactionID) -> Result<bool> {
        self.rollback_map().contains_key_confirmed(transaction_id)
    }

    /// Returns the rollback operations for the given `transaction ID`.
    fn get_rollback_operations_speculative(
        &self,
        transaction_id: &N::TransactionID,
    ) -> Result<Option<Vec<RollbackOperation<N>>>> {
        match self.rollback_map().get_speculative(transaction_id)? {
            Some(mapping_id) => Ok(Some(cow_to_cloned!(mapping_id))),
            None => Ok(None),
        }
    }
}

/// The rollback store.
#[derive(Clone)]
pub struct RollbackStore<N: Network, R: RollbackStorage<N>> {
    /// The rollback storage.
    storage: R,
    /// PhantomData.
    _phantom: PhantomData<N>,
}

impl<N: Network, R: RollbackStorage<N>> RollbackStore<N, R> {
    /// Initializes the rollback store.
    pub fn open(dev: Option<u16>) -> Result<Self> {
        Self::from(R::open(dev)?)
    }

    /// Initializes a rollback store from storage.
    pub fn from(storage: R) -> Result<Self> {
        // Return the rollback store.
        Ok(Self { storage, _phantom: PhantomData })
    }

    /// Inserts the rollback operations for the given `transaction ID` into storage.
    pub fn insert_rollback_operations(
        &self,
        transaction_id: &N::TransactionID,
        rollback_operations: Vec<RollbackOperation<N>>,
    ) -> Result<()> {
        self.storage.insert_rollback_operations(transaction_id, rollback_operations)
    }

    /// Removes the rollback operations for the given transaction ID.
    pub fn remove_rollback_operations(&self, transaction_id: &N::TransactionID) -> Result<()> {
        self.storage.remove_rollback_operations(transaction_id)
    }

    /// Starts an atomic batch write operation.
    pub fn start_atomic(&self) {
        self.storage.start_atomic();
    }

    /// Checks if an atomic batch is in progress.
    pub fn is_atomic_in_progress(&self) -> bool {
        self.storage.is_atomic_in_progress()
    }

    /// Checkpoints the atomic batch.
    pub fn atomic_checkpoint(&self) {
        self.storage.atomic_checkpoint();
    }

    /// Clears the latest atomic batch checkpoint.
    pub fn clear_latest_checkpoint(&self) {
        self.storage.clear_latest_checkpoint();
    }

    /// Rewinds the atomic batch to the previous checkpoint.
    pub fn atomic_rewind(&self) {
        self.storage.atomic_rewind();
    }

    /// Aborts an atomic batch write operation.
    pub fn abort_atomic(&self) {
        self.storage.abort_atomic();
    }

    /// Finishes an atomic batch write operation.
    pub fn finish_atomic(&self) -> Result<()> {
        self.storage.finish_atomic()
    }

    /// Returns the optional development ID.
    pub fn dev(&self) -> Option<u16> {
        self.storage.dev()
    }
}

impl<N: Network, R: RollbackStorage<N>> RollbackStore<N, R> {
    /// Returns `true` if the given `transaction ID` exists.
    pub fn contains_transaction_id_confirmed(&self, transaction_id: &N::TransactionID) -> Result<bool> {
        self.storage.contains_transaction_id_confirmed(transaction_id)
    }
}

impl<N: Network, R: RollbackStorage<N>> RollbackStore<N, R> {
    /// Returns the rollback operations for the given `transaction ID`.
    pub fn get_rollback_operations_speculative(
        &self,
        transaction_id: &N::TransactionID,
    ) -> Result<Option<Vec<RollbackOperation<N>>>> {
        self.storage.get_rollback_operations_speculative(transaction_id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{helpers::memory::RollbackMemory, Transaction};

    #[test]
    fn test_insert_get_remove() {
        let mut rng = TestRng::default();

        // Sample the deployment transaction.
        let transaction = crate::vm::test_helpers::sample_deployment_transaction(&mut rng);

        assert!(matches!(transaction, Transaction::Deploy(_, _, _, _)), "Expected a deployment transaction.");
        if let Transaction::Deploy(transaction_id, _, deployment, _) = transaction {
            // Initialize the VM.
            let vm = crate::vm::test_helpers::sample_vm();

            let (_, _, rollback_operations) =
                vm.process().write().finalize_deployment(vm.finalize_store(), &deployment).unwrap();

            // Initialize a new rollback store.
            let rollback_store = RollbackStore::<_, RollbackMemory<_>>::open(None).unwrap();

            // Ensure the rollback operations do not exist.
            let candidate = rollback_store.get_rollback_operations_speculative(&transaction_id).unwrap();
            assert_eq!(None, candidate);

            // Insert the rollback operations.
            rollback_store.insert_rollback_operations(&transaction_id, rollback_operations.clone()).unwrap();

            // Retrieve the rollback operations.
            let candidate = rollback_store.get_rollback_operations_speculative(&transaction_id).unwrap();
            assert_eq!(Some(rollback_operations), candidate);

            // Remove the rollback operations.
            rollback_store.remove_rollback_operations(&transaction_id).unwrap();

            // Ensure the rollback operations do not exist.
            let candidate = rollback_store.get_rollback_operations_speculative(&transaction_id).unwrap();
            assert_eq!(None, candidate);
        }
    }
}
