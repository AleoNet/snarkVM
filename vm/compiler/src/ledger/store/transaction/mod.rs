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

use crate::ledger::{
    map::{memory_map::MemoryMap, Map, MapRead},
    Deployment,
    Origin,
    Transaction,
    Transition,
};

use console::{
    network::prelude::*,
    types::{Field, Group},
};

use anyhow::Result;
use std::borrow::Cow;

/// A trait for transaction storage.
pub trait TransactionStorage<N: Network>: Clone {
    type DeploymentsMap: for<'a> Map<'a, N::TransactionID, (Deployment<N>, N::TransitionID)>;
    type ExecutionsMap: for<'a> Map<'a, N::TransactionID, (Vec<N::TransitionID>, Option<N::TransitionID>)>;
    type TransitionsMap: for<'a> Map<'a, N::TransitionID, Transition<N>>;
    type TransitionPublicKeysMap: for<'a> Map<'a, Group<N>, N::TransitionID>;
    type SerialNumbersMap: for<'a> Map<'a, Field<N>, N::TransitionID>;
    type CommitmentsMap: for<'a> Map<'a, Field<N>, N::TransitionID>;
    type OriginsMap: for<'a> Map<'a, Origin<N>, N::TransitionID>;
    type NonceMap: for<'a> Map<'a, Group<N>, N::TransitionID>;
}

/// An in-memory transaction storage.
#[derive(Clone)]
pub struct TransactionMemory<N: Network>(core::marker::PhantomData<N>);

#[rustfmt::skip]
impl<N: Network> TransactionStorage<N> for TransactionMemory<N> {
    type DeploymentsMap = MemoryMap<N::TransactionID, (Deployment<N>, N::TransitionID)>;
    type ExecutionsMap = MemoryMap<N::TransactionID, (Vec<N::TransitionID>, Option<N::TransitionID>)>;
    type TransitionsMap = MemoryMap<N::TransitionID, Transition<N>>;
    type TransitionPublicKeysMap = MemoryMap<Group<N>, N::TransitionID>;
    type SerialNumbersMap = MemoryMap<Field<N>, N::TransitionID>;
    type CommitmentsMap = MemoryMap<Field<N>, N::TransitionID>;
    type OriginsMap = MemoryMap<Origin<N>, N::TransitionID>;
    type NonceMap = MemoryMap<Group<N>, N::TransitionID>;
}

/// The transaction state stored in a ledger.
/// `TransitionPublicKeysMap`, `SerialNumbersMap`, `CommitmentsMap`, `OriginsMap`, and `NonceMap` store redundant data for faster lookup.
#[derive(Clone)]
pub struct TransactionStore<N: Network, T: TransactionStorage<N>> {
    /// The map of program deployments.
    deployments: T::DeploymentsMap,
    /// The map of program executions.
    executions: T::ExecutionsMap,
    /// The map of transitions.
    transitions: T::TransitionsMap,
}

impl<N: Network> TransactionStore<N, TransactionMemory<N>> {
    /// Initializes a new instance of `TransactionStore`.
    pub fn new() -> Self {
        Self { deployments: Default::default(), executions: Default::default(), transitions: Default::default() }
    }
}

impl<N: Network, T: TransactionStorage<N>> TransactionStore<N, T> {
    /// Initializes a new instance of `TransactionStore` from the given maps.
    pub fn from_maps(
        deployments: T::DeploymentsMap,
        executions: T::ExecutionsMap,
        transitions: T::TransitionsMap,
    ) -> Result<Self> {
        let transaction_store = Self { deployments, executions, transitions };

        // TODO (raychu86): Enforce that all the transaction state is valid.

        Ok(transaction_store)
    }

    // /// Checks the given transaction is well formed and unique.
    // pub fn check_transaction(&self, transaction: &Transaction<N>) -> Result<()> {
    //     let transaction_id = transaction.id();
    //     if self.contains_transaction_id(&transaction_id)? {
    //         bail!("Transaction '{transaction_id}' already exists in the ledger")
    //     }
    //
    //     // Ensure the ledger does not already contain a given transition public keys.
    //     for tpk in transaction.transition_public_keys() {
    //         if self.contains_transition_public_key(tpk)? {
    //             bail!("Transition public key '{tpk}' already exists in the ledger")
    //         }
    //     }
    //
    //     // Ensure that the origin are valid.
    //     for origin in transaction.origins() {
    //         if !self.contains_origin(origin)? {
    //             bail!("The given transaction references a non-existent origin {}", &origin)
    //         }
    //
    //         match origin {
    //             // Check that the commitment exists in the ledger.
    //             Origin::Commitment(commitment) => {
    //                 if !self.contains_commitment(commitment)? {
    //                     bail!("The given transaction references a non-existent commitment {}", &commitment)
    //                 }
    //             }
    //             // TODO (raychu86): Ensure that the state root exists in the ledger.
    //             // Check that the state root is an existing state root.
    //             Origin::StateRoot(_state_root) => {
    //                 bail!("State roots are currently not supported (yet)")
    //             }
    //         }
    //     }
    //
    //     // Ensure the ledger does not already contain a given serial numbers.
    //     for serial_number in transaction.serial_numbers() {
    //         if self.contains_serial_number(serial_number)? {
    //             bail!("Serial number '{serial_number}' already exists in the ledger")
    //         }
    //     }
    //
    //     // Ensure the ledger does not already contain a given commitments.
    //     for commitment in transaction.commitments() {
    //         if self.contains_commitment(commitment)? {
    //             bail!("Commitment '{commitment}' already exists in the ledger")
    //         }
    //     }
    //
    //     // Ensure the ledger does not already contain a given nonces.
    //     for nonce in transaction.nonces() {
    //         if self.contains_nonce(nonce)? {
    //             bail!("Nonce '{nonce}' already exists in the ledger")
    //         }
    //     }
    //
    //     Ok(())
    // }
    //
    // /// Adds the given transaction to the transaction store.
    // pub fn insert(&mut self, transaction: Transaction<N>) -> Result<()> {
    //     // Check that there are not collisions with existing transactions.
    //     self.check_transaction(&transaction)?;
    //
    //     /* ATOMIC CODE SECTION */
    //
    //     // Insert the transaction. This code section executes atomically.
    //     {
    //         let mut transaction_store = self.clone();
    //
    //         for transition in transaction.transitions() {
    //             let transition_id = transition.id();
    //
    //             // Insert the transitions.
    //             transaction_store.transitions.insert(*transition_id, transition.clone())?;
    //
    //             // Insert the transition public key.
    //             transaction_store.transition_public_keys.insert(*transition.tpk(), *transition_id)?;
    //
    //             // Insert the serial numbers.
    //             for serial_number in transition.serial_numbers() {
    //                 transaction_store.serial_numbers.insert(*serial_number, *transition_id)?;
    //             }
    //
    //             // Insert the commitments.
    //             for commitment in transition.commitments() {
    //                 transaction_store.commitments.insert(*commitment, *transition_id)?;
    //             }
    //
    //             // Insert the origins.
    //             for origin in transition.origins() {
    //                 transaction_store.origins.insert(*origin, *transition_id)?;
    //             }
    //
    //             // Insert the nonces.
    //             for nonce in transition.nonces() {
    //                 transaction_store.nonces.insert(*nonce, *transition_id)?;
    //             }
    //         }
    //
    //         // Insert the deployment or execution.
    //         match transaction {
    //             Transaction::Deploy(transaction_id, deployment, additional_fee) => {
    //                 transaction_store.deployments.insert(transaction_id, (deployment, *additional_fee.id()))?;
    //             }
    //             Transaction::Execute(transaction_id, execution, additional_fee) => {
    //                 let transition_ids = execution.iter().map(|transition| *transition.id()).collect();
    //
    //                 transaction_store
    //                     .executions
    //                     .insert(transaction_id, (transition_ids, additional_fee.map(|t| *t.id())))?;
    //             }
    //         }
    //
    //         *self = Self {
    //             deployments: transaction_store.deployments,
    //             executions: transaction_store.executions,
    //             transitions: transaction_store.transitions,
    //             transition_public_keys: transaction_store.transition_public_keys,
    //             origins: transaction_store.origins,
    //             serial_numbers: transaction_store.serial_numbers,
    //             commitments: transaction_store.commitments,
    //             nonces: transaction_store.nonces,
    //         };
    //     }
    //
    //     Ok(())
    // }
}

impl<N: Network, T: TransactionStorage<N>> TransactionStore<N, T> {
    /// Returns an iterator over the transaction IDs, for all transitions in `self`.
    pub fn transaction_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, N::TransactionID>> {
        self.deployments.keys().chain(self.executions.keys())
    }

    /// Returns an iterator over all transactions in `self` that are deployments.
    pub fn deployments(&self) -> impl '_ + Iterator<Item = Cow<'_, Deployment<N>>> {
        self.deployments.values().map(|tx| match tx {
            Cow::Borrowed((deployment, _)) => Cow::Borrowed(deployment),
            Cow::Owned((deployment, _)) => Cow::Owned(deployment),
        })
    }

    // TODO (raychu86): Implement iterators for executions.
    // /// Returns an iterator over all transactions in `self` that are executions.
    // pub fn executions(&self) -> impl '_ + Iterator<Item = Cow<'_, Execution<N>>> {
    //
    // }
}

impl<N: Network, T: TransactionStorage<N>> TransactionStore<N, T> {
    /// Returns `true` if the given transaction exists.
    pub fn contains_transaction(&self, transaction: &Transaction<N>) -> Result<bool> {
        self.contains_transaction_id(&transaction.id())
    }

    /// Returns `true` if the given transaction ID exists.
    pub fn contains_transaction_id(&self, transaction_id: &N::TransactionID) -> Result<bool> {
        self.deployments.contains_key(transaction_id).or_else(|_| self.executions.contains_key(transaction_id))
    }
}

use crate::Execution;
use core::borrow::Borrow;

impl<N: Network, T: TransactionStorage<N>> TransactionStore<N, T> {
    /// Returns the transaction for the given transaction id.
    pub fn get_transaction(&self, transaction_id: N::TransactionID) -> Result<Transaction<N>> {
        if let Some(value) = self.deployments.get(&transaction_id)? {
            // Return the deployment transaction.
            let (deployment, additional_fee) = value.borrow();
            Transaction::from_deployment(deployment.clone(), self.get_transition(*additional_fee)?.into_owned())
        } else if let Some(value) = self.executions.get(&transaction_id)? {
            // Return the execution transaction.
            let (execution, additional_fee) = value.borrow();

            let transitions: Result<Vec<_>> = execution
                .iter()
                .map(|transition_id| self.get_transition(*transition_id).map(|t| t.into_owned()))
                .collect();
            let execution = Execution::from(N::ID, &transitions?)?;
            let additional_fee = match additional_fee {
                Some(transition_id) => Some(self.get_transition(*transition_id)?.into_owned()),
                None => None,
            };

            Transaction::from_execution(execution, additional_fee)
        } else {
            bail!("Missing transaction with id {transaction_id}")
        }
    }

    /// Returns the transactions for the given transition id.
    pub fn get_transition(&self, transition_id: N::TransitionID) -> Result<Cow<'_, Transition<N>>> {
        match self.transitions.get(&transition_id)? {
            Some(transition) => Ok(transition),
            None => bail!("Missing transition with id {transition_id}"),
        }
    }

    // // TODO (raychu86): Rename this.
    // /// Returns the transactions for the given commitment.
    // pub fn get_transition_id_from_commitment(&self, commitment: N::TransitionID) -> Result<Cow<'_, N::TransitionID>> {
    //     match self.commitments.get(&commitment)? {
    //         Some(transition_id) => Ok(transition_id),
    //         None => bail!("Missing commitment {commitment}"),
    //     }
    // }
}
