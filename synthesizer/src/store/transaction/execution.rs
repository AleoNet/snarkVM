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

use crate::{
    atomic_write_batch,
    block::{Transaction, Transition},
    cow_to_cloned,
    cow_to_copied,
    process::{Execution, Fee},
    snark::Proof,
    store::{
        helpers::{memory_map::MemoryMap, Map, MapRead},
        TransitionMemory,
        TransitionStorage,
        TransitionStore,
    },
};
use console::network::prelude::*;

use anyhow::Result;
use core::marker::PhantomData;
use std::borrow::Cow;

/// A trait for execution storage.
pub trait ExecutionStorage<N: Network>: Clone + Send + Sync {
    /// The mapping of `transaction ID` to `([transition ID], (optional) transition ID)`.
    type IDMap: for<'a> Map<'a, N::TransactionID, (Vec<N::TransitionID>, Option<N::TransitionID>)>;
    /// The mapping of `transition ID` to `transaction ID`.
    type ReverseIDMap: for<'a> Map<'a, N::TransitionID, N::TransactionID>;
    /// The transition storage.
    type TransitionStorage: TransitionStorage<N>;
    /// The mapping of `transaction ID` to `(global state root, (optional) inclusion proof)`.
    type InclusionMap: for<'a> Map<'a, N::TransactionID, (N::StateRoot, Option<Proof<N>>)>;
    /// The mapping of `transaction ID` to `(global state root, (optional) inclusion proof)`.
    type FeeMap: for<'a> Map<'a, N::TransactionID, (N::StateRoot, Option<Proof<N>>)>;

    /// Initializes the execution storage.
    fn open(transition_store: TransitionStore<N, Self::TransitionStorage>) -> Result<Self>;

    /// Returns the ID map.
    fn id_map(&self) -> &Self::IDMap;
    /// Returns the reverse ID map.
    fn reverse_id_map(&self) -> &Self::ReverseIDMap;
    /// Returns the transition store.
    fn transition_store(&self) -> &TransitionStore<N, Self::TransitionStorage>;
    /// Returns the inclusion map.
    fn inclusion_map(&self) -> &Self::InclusionMap;
    /// Returns the fee map.
    fn fee_map(&self) -> &Self::FeeMap;

    /// Returns the optional development ID.
    fn dev(&self) -> Option<u16> {
        self.transition_store().dev()
    }

    /// Starts an atomic batch write operation.
    fn start_atomic(&self) {
        self.id_map().start_atomic();
        self.reverse_id_map().start_atomic();
        self.transition_store().start_atomic();
        self.inclusion_map().start_atomic();
        self.fee_map().start_atomic();
    }

    /// Checks if an atomic batch is in progress.
    fn is_atomic_in_progress(&self) -> bool {
        self.id_map().is_atomic_in_progress()
            || self.reverse_id_map().is_atomic_in_progress()
            || self.transition_store().is_atomic_in_progress()
            || self.inclusion_map().is_atomic_in_progress()
            || self.fee_map().is_atomic_in_progress()
    }

    /// Aborts an atomic batch write operation.
    fn abort_atomic(&self) {
        self.id_map().abort_atomic();
        self.reverse_id_map().abort_atomic();
        self.transition_store().abort_atomic();
        self.inclusion_map().abort_atomic();
        self.fee_map().abort_atomic();
    }

    /// Finishes an atomic batch write operation.
    fn finish_atomic(&self) -> Result<()> {
        self.id_map().finish_atomic()?;
        self.reverse_id_map().finish_atomic()?;
        self.transition_store().finish_atomic()?;
        self.inclusion_map().finish_atomic()?;
        self.fee_map().finish_atomic()
    }

    /// Stores the given `execution transaction` pair into storage.
    fn insert(&self, transaction: &Transaction<N>) -> Result<()> {
        // Ensure the transaction is a execution.
        let (transaction_id, execution, optional_additional_fee) = match transaction {
            Transaction::Deploy(..) => {
                bail!("Attempted to insert non-execution transaction into execution storage.")
            }
            Transaction::Execute(transaction_id, execution, optional_additional_fee) => {
                (transaction_id, execution, optional_additional_fee)
            }
        };

        // Retrieve the transitions.
        let transitions = execution.transitions();
        // Retrieve the transition IDs.
        let transition_ids = execution.transitions().map(Transition::id).copied().collect();
        // Retrieve the global state root.
        let global_state_root = execution.global_state_root();
        // Retrieve the inclusion proof.
        let inclusion_proof = execution.inclusion_proof().cloned();

        // Retrieve the optional additional fee ID.
        let optional_additional_fee_id = optional_additional_fee.as_ref().map(|additional_fee| *additional_fee.id());

        atomic_write_batch!(self, {
            // Store the transition IDs.
            self.id_map().insert(*transaction_id, (transition_ids, optional_additional_fee_id))?;

            // Store the execution.
            for transition in transitions {
                // Store the transition ID.
                self.reverse_id_map().insert(*transition.id(), *transaction_id)?;
                // Store the transition.
                self.transition_store().insert(transition)?;
            }

            // Store the global state root and inclusion proof.
            self.inclusion_map().insert(*transaction_id, (global_state_root, inclusion_proof))?;

            // Store the additional fee, if one exists.
            if let Some(additional_fee) = optional_additional_fee {
                // Store the additional fee ID.
                self.reverse_id_map().insert(*additional_fee.transition_id(), *transaction_id)?;
                // Store the additional fee transition.
                self.transition_store().insert(additional_fee)?;
                // Store the additional fee.
                self.fee_map().insert(
                    *transaction_id,
                    (additional_fee.global_state_root(), additional_fee.inclusion_proof().cloned()),
                )?;
            }

            Ok(())
        });

        Ok(())
    }

    /// Removes the execution transaction for the given `transaction ID`.
    fn remove(&self, transaction_id: &N::TransactionID) -> Result<()> {
        // Retrieve the transition IDs and optional additional fee ID.
        let (transition_ids, optional_additional_fee_id) = match self.id_map().get(transaction_id)? {
            Some(ids) => cow_to_cloned!(ids),
            None => bail!("Failed to get the transition IDs for the transaction '{transaction_id}'"),
        };

        atomic_write_batch!(self, {
            // Remove the transition IDs.
            self.id_map().remove(transaction_id)?;

            // Remove the execution.
            for transition_id in transition_ids {
                // Remove the transition ID.
                self.reverse_id_map().remove(&transition_id)?;
                // Remove the transition.
                self.transition_store().remove(&transition_id)?;
            }

            // Remove the global state root and inclusion proof.
            self.inclusion_map().remove(transaction_id)?;

            // Remove the additional fee ID, if one exists.
            if let Some(additional_fee_id) = optional_additional_fee_id {
                // Remove the additional fee ID.
                self.reverse_id_map().remove(&additional_fee_id)?;
                // Remove the additional fee transition.
                self.transition_store().remove(&additional_fee_id)?;
                // Remove the additional fee.
                self.fee_map().remove(transaction_id)?;
            }

            Ok(())
        });

        Ok(())
    }

    /// Returns the transaction ID that contains the given `transition ID`.
    fn find_transaction_id(&self, transition_id: &N::TransitionID) -> Result<Option<N::TransactionID>> {
        match self.reverse_id_map().get(transition_id)? {
            Some(transaction_id) => Ok(Some(cow_to_copied!(transaction_id))),
            None => Ok(None),
        }
    }

    /// Returns the execution for the given `transaction ID`.
    fn get_execution(&self, transaction_id: &N::TransactionID) -> Result<Option<Execution<N>>> {
        // Retrieve the transition IDs and optional additional fee ID.
        let (transition_ids, _) = match self.id_map().get(transaction_id)? {
            Some(ids) => cow_to_cloned!(ids),
            None => return Ok(None),
        };

        // Retrieve the global state root and inclusion proof.
        let (global_state_root, inclusion_proof) = match self.inclusion_map().get(transaction_id)? {
            Some(inclusion) => cow_to_cloned!(inclusion),
            None => bail!("Failed to get the inclusion proof for the transaction '{transaction_id}'"),
        };

        // Initialize a vector for the transitions.
        let mut transitions = Vec::new();

        // Retrieve the transitions.
        for transition_id in &transition_ids {
            match self.transition_store().get_transition(transition_id)? {
                Some(transition) => transitions.push(transition),
                None => bail!("Failed to get transition '{transition_id}' for transaction '{transaction_id}'"),
            };
        }

        // Return the execution.
        Ok(Some(Execution::from(transitions.into_iter(), global_state_root, inclusion_proof)?))
    }

    /// Returns the transaction for the given `transaction ID`.
    fn get_transaction(&self, transaction_id: &N::TransactionID) -> Result<Option<Transaction<N>>> {
        // Retrieve the transition IDs and optional additional fee ID.
        let (transition_ids, optional_additional_fee_id) = match self.id_map().get(transaction_id)? {
            Some(ids) => cow_to_cloned!(ids),
            None => return Ok(None),
        };

        // Retrieve the global state root and inclusion proof.
        let (global_state_root, inclusion_proof) = match self.inclusion_map().get(transaction_id)? {
            Some(inclusion) => cow_to_cloned!(inclusion),
            None => bail!("Failed to get the inclusion proof for the transaction '{transaction_id}'"),
        };

        // Initialize a vector for the transitions.
        let mut transitions = Vec::new();

        // Retrieve the transitions.
        for transition_id in &transition_ids {
            match self.transition_store().get_transition(transition_id)? {
                Some(transition) => transitions.push(transition),
                None => bail!("Failed to get transition '{transition_id}' for transaction '{transaction_id}'"),
            };
        }

        // Construct the execution.
        let execution = Execution::from(transitions.into_iter(), global_state_root, inclusion_proof)?;

        // Construct the transaction.
        let transaction = match optional_additional_fee_id {
            Some(additional_fee_id) => {
                // Retrieve the additional fee transition.
                let additional_fee_transition = match self.transition_store().get_transition(&additional_fee_id)? {
                    Some(additional_fee_transition) => additional_fee_transition,
                    None => bail!("Failed to get the additional fee for transaction '{transaction_id}'"),
                };
                // Retrieve the additional fee.
                let (global_state_root, inclusion_proof) = match self.fee_map().get(&additional_fee_id)? {
                    Some(fee) => cow_to_cloned!(fee),
                    None => bail!("Failed to get the additional fee for transaction '{transaction_id}'"),
                };
                // Construct the transaction.
                Transaction::from_execution(
                    execution,
                    Some(Fee::from(additional_fee_transition, global_state_root, inclusion_proof)),
                )?
            }
            None => Transaction::from_execution(execution, None)?,
        };

        // Ensure the transaction ID matches.
        match *transaction_id == transaction.id() {
            true => Ok(Some(transaction)),
            false => bail!("Mismatching transaction ID for transaction '{transaction_id}'"),
        }
    }
}

/// An in-memory execution storage.
#[derive(Clone)]
#[allow(clippy::type_complexity)]
pub struct ExecutionMemory<N: Network> {
    /// The ID map.
    id_map: MemoryMap<N::TransactionID, (Vec<N::TransitionID>, Option<N::TransitionID>)>,
    /// The reverse ID map.
    reverse_id_map: MemoryMap<N::TransitionID, N::TransactionID>,
    /// The transition store.
    transition_store: TransitionStore<N, TransitionMemory<N>>,
    /// The inclusion map.
    inclusion_map: MemoryMap<N::TransactionID, (N::StateRoot, Option<Proof<N>>)>,
    /// The fee map.
    fee_map: MemoryMap<N::TransactionID, (N::StateRoot, Option<Proof<N>>)>,
}

#[rustfmt::skip]
impl<N: Network> ExecutionStorage<N> for ExecutionMemory<N> {
    type IDMap = MemoryMap<N::TransactionID, (Vec<N::TransitionID>, Option<N::TransitionID>)>;
    type ReverseIDMap = MemoryMap<N::TransitionID, N::TransactionID>;
    type TransitionStorage = TransitionMemory<N>;
    type InclusionMap = MemoryMap<N::TransactionID, (N::StateRoot, Option<Proof<N>>)>;
    type FeeMap = MemoryMap<N::TransactionID, (N::StateRoot, Option<Proof<N>>)>;

    /// Initializes the execution storage.
    fn open(transition_store: TransitionStore<N, Self::TransitionStorage>) -> Result<Self> {
        Ok(Self {
            id_map: MemoryMap::default(),
            reverse_id_map: MemoryMap::default(),
            transition_store,
            inclusion_map: MemoryMap::default(),
            fee_map: MemoryMap::default(),
        })
    }

    /// Returns the ID map.
    fn id_map(&self) -> &Self::IDMap {
        &self.id_map
    }

    /// Returns the reverse ID map.
    fn reverse_id_map(&self) -> &Self::ReverseIDMap {
        &self.reverse_id_map
    }

    /// Returns the transition store.
    fn transition_store(&self) -> &TransitionStore<N, Self::TransitionStorage> {
        &self.transition_store
    }

    /// Returns the inclusion map.
    fn inclusion_map(&self) -> &Self::InclusionMap {
        &self.inclusion_map
    }

    /// Returns the fee map.
    fn fee_map(&self) -> &Self::FeeMap {
        &self.fee_map
    }
}

/// The execution store.
#[derive(Clone)]
pub struct ExecutionStore<N: Network, E: ExecutionStorage<N>> {
    /// The execution storage.
    storage: E,
    /// PhantomData.
    _phantom: PhantomData<N>,
}

impl<N: Network, E: ExecutionStorage<N>> ExecutionStore<N, E> {
    /// Initializes the execution store.
    pub fn open(transition_store: TransitionStore<N, E::TransitionStorage>) -> Result<Self> {
        // Initialize the execution storage.
        let storage = E::open(transition_store)?;
        // Return the execution store.
        Ok(Self { storage, _phantom: PhantomData })
    }

    /// Initializes an execution store from storage.
    pub fn from(storage: E) -> Self {
        Self { storage, _phantom: PhantomData }
    }

    /// Stores the given `execution transaction` into storage.
    pub fn insert(&self, transaction: &Transaction<N>) -> Result<()> {
        self.storage.insert(transaction)
    }

    /// Removes the transaction for the given `transaction ID`.
    pub fn remove(&self, transaction_id: &N::TransactionID) -> Result<()> {
        self.storage.remove(transaction_id)
    }

    /// Returns the transition store.
    pub fn transition_store(&self) -> &TransitionStore<N, E::TransitionStorage> {
        self.storage.transition_store()
    }

    /// Starts an atomic batch write operation.
    pub fn start_atomic(&self) {
        self.storage.start_atomic();
    }

    /// Checks if an atomic batch is in progress.
    pub fn is_atomic_in_progress(&self) -> bool {
        self.storage.is_atomic_in_progress()
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

impl<N: Network, E: ExecutionStorage<N>> ExecutionStore<N, E> {
    /// Returns the transaction for the given `transaction ID`.
    pub fn get_transaction(&self, transaction_id: &N::TransactionID) -> Result<Option<Transaction<N>>> {
        self.storage.get_transaction(transaction_id)
    }

    /// Returns the execution for the given `transaction ID`.
    pub fn get_execution(&self, transaction_id: &N::TransactionID) -> Result<Option<Execution<N>>> {
        self.storage.get_execution(transaction_id)
    }
}

impl<N: Network, E: ExecutionStorage<N>> ExecutionStore<N, E> {
    /// Returns the transaction ID that executed the given `transition ID`.
    pub fn find_transaction_id(&self, transition_id: &N::TransitionID) -> Result<Option<N::TransactionID>> {
        self.storage.find_transaction_id(transition_id)
    }
}

impl<N: Network, E: ExecutionStorage<N>> ExecutionStore<N, E> {
    /// Returns an iterator over the execution transaction IDs, for all executions.
    pub fn execution_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, N::TransactionID>> {
        self.storage.id_map().keys()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_insert_get_remove() {
        let rng = &mut TestRng::default();

        // Sample the execution transaction.
        let transaction = crate::vm::test_helpers::sample_execution_transaction(rng);
        let transaction_id = transaction.id();

        // Initialize a new transition store.
        let transition_store = TransitionStore::open(None).unwrap();
        // Initialize a new execution store.
        let execution_store = ExecutionMemory::open(transition_store).unwrap();

        // Ensure the execution transaction does not exist.
        let candidate = execution_store.get_transaction(&transaction_id).unwrap();
        assert_eq!(None, candidate);

        // Insert the execution transaction.
        execution_store.insert(&transaction).unwrap();

        // Retrieve the execution transaction.
        let candidate = execution_store.get_transaction(&transaction_id).unwrap();
        assert_eq!(Some(transaction), candidate);

        // Remove the execution.
        execution_store.remove(&transaction_id).unwrap();

        // Ensure the execution transaction does not exist.
        let candidate = execution_store.get_transaction(&transaction_id).unwrap();
        assert_eq!(None, candidate);
    }

    #[test]
    fn test_find_transaction_id() {
        let rng = &mut TestRng::default();

        // Sample the execution transaction.
        let transaction = crate::vm::test_helpers::sample_execution_transaction(rng);
        let transaction_id = transaction.id();
        let transition_ids = match transaction {
            Transaction::Execute(_, ref execution, _) => {
                execution.transitions().map(|transition| *transition.id()).collect::<Vec<_>>()
            }
            _ => panic!("Incorrect transaction type"),
        };

        // Initialize a new transition store.
        let transition_store = TransitionStore::open(None).unwrap();
        // Initialize a new execution store.
        let execution_store = ExecutionMemory::open(transition_store).unwrap();

        // Ensure the execution transaction does not exist.
        let candidate = execution_store.get_transaction(&transaction_id).unwrap();
        assert_eq!(None, candidate);

        for transition_id in transition_ids {
            // Ensure the transaction ID is not found.
            let candidate = execution_store.find_transaction_id(&transition_id).unwrap();
            assert_eq!(None, candidate);

            // Insert the execution.
            execution_store.insert(&transaction).unwrap();

            // Find the transaction ID.
            let candidate = execution_store.find_transaction_id(&transition_id).unwrap();
            assert_eq!(Some(transaction_id), candidate);

            // Remove the execution.
            execution_store.remove(&transaction_id).unwrap();

            // Ensure the transaction ID is not found.
            let candidate = execution_store.find_transaction_id(&transition_id).unwrap();
            assert_eq!(None, candidate);
        }
    }
}
