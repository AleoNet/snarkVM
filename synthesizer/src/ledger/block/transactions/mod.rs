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

mod merkle;
pub use merkle::*;

mod bytes;
mod serialize;
mod string;

use crate::{
    ledger::{Origin, Transaction, Transition},
    process::{Deployment, Execution},
};
use console::{
    collections::merkle_tree::MerklePath,
    network::{prelude::*, BHPMerkleTree},
    types::{Field, Group},
};

use indexmap::IndexMap;

#[derive(Clone, PartialEq, Eq)]
pub struct Transactions<N: Network> {
    /// The transactions included in a block.
    transactions: IndexMap<N::TransactionID, Transaction<N>>,
}

impl<N: Network> Transactions<N> {
    /// Initializes from a given transactions list.
    pub fn from(transactions: &[Transaction<N>]) -> Self {
        Self::from_iter(transactions.iter())
    }
}

impl<N: Network> FromIterator<Transaction<N>> for Transactions<N> {
    /// Initializes from an iterator of transactions.
    fn from_iter<T: IntoIterator<Item = Transaction<N>>>(iter: T) -> Self {
        Self { transactions: iter.into_iter().map(|transaction| (transaction.id(), transaction)).collect() }
    }
}

impl<'a, N: Network> FromIterator<&'a Transaction<N>> for Transactions<N> {
    /// Initializes from an iterator of transactions.
    fn from_iter<T: IntoIterator<Item = &'a Transaction<N>>>(iter: T) -> Self {
        Self::from_iter(iter.into_iter().cloned())
    }
}

impl<N: Network> Transactions<N> {
    /// The maximum number of transactions allowed in a block.
    pub const MAX_TRANSACTIONS: usize = usize::pow(2, TRANSACTIONS_DEPTH as u32);

    /// Returns an iterator over all transactions, for all transactions in `self`.
    pub fn transactions(&self) -> impl '_ + Iterator<Item = &Transaction<N>> {
        self.transactions.values()
    }

    /// Returns an iterator over the transaction IDs, for all transactions in `self`.
    pub fn transaction_ids(&self) -> impl '_ + Iterator<Item = &N::TransactionID> {
        self.transactions.keys()
    }

    /// Returns an iterator over all transactions in `self` that are deployments.
    pub fn deployments(&self) -> impl '_ + Iterator<Item = &Deployment<N>> {
        self.transactions().filter_map(|transaction| match transaction {
            Transaction::Deploy(_, deployment, _) => Some(deployment.as_ref()),
            _ => None,
        })
    }

    /// Returns an iterator over all transactions in `self` that are executions.
    pub fn executions(&self) -> impl '_ + Iterator<Item = &Execution<N>> {
        self.transactions().filter_map(|transaction| match transaction {
            Transaction::Execute(_, execution, _) => Some(execution),
            _ => None,
        })
    }

    /// Returns an iterator over all transitions.
    pub fn transitions(&self) -> impl '_ + Iterator<Item = &Transition<N>> {
        self.transactions().flat_map(Transaction::transitions)
    }

    /// Returns an iterator over the transition IDs, for all transitions.
    pub fn transition_ids(&self) -> impl '_ + Iterator<Item = &N::TransitionID> {
        self.transactions().flat_map(Transaction::transition_ids)
    }

    /// Returns an iterator over the transition public keys, for all transactions.
    pub fn transition_public_keys(&self) -> impl '_ + Iterator<Item = &Group<N>> {
        self.transactions().flat_map(Transaction::transition_public_keys)
    }

    /// Returns an iterator over the origins, for all transition inputs that are records.
    pub fn origins(&self) -> impl '_ + Iterator<Item = &Origin<N>> {
        self.transitions().flat_map(Transition::origins)
    }

    /// Returns an iterator over the tags, for all transition inputs that are records.
    pub fn tags(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transitions().flat_map(Transition::tags)
    }

    /// Returns an iterator over the serial numbers, for all transition inputs that are records.
    pub fn serial_numbers(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transitions().flat_map(Transition::serial_numbers)
    }

    /// Returns an iterator over the commitments, for all transition outputs that are records.
    pub fn commitments(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transitions().flat_map(Transition::commitments)
    }

    /// Returns an iterator over the nonces, for all transition outputs that are records.
    pub fn nonces(&self) -> impl '_ + Iterator<Item = &Group<N>> {
        self.transitions().flat_map(Transition::nonces)
    }

    /// Returns an iterator over the fees, for all transitions.
    pub fn fees(&self) -> impl '_ + Iterator<Item = &i64> {
        self.transitions().map(Transition::fee)
    }
}

impl<N: Network> Transactions<N> {
    /// Returns a consuming iterator over all transactions, for all transactions in `self`.
    pub fn into_transactions(self) -> impl Iterator<Item = Transaction<N>> {
        self.transactions.into_values()
    }

    /// Returns a consuming iterator over the transaction IDs, for all transactions in `self`.
    pub fn into_transaction_ids(self) -> impl Iterator<Item = N::TransactionID> {
        self.transactions.into_keys()
    }

    /// Returns a consuming iterator over all transactions in `self` that are deployments.
    pub fn into_deployments(self) -> impl Iterator<Item = Deployment<N>> {
        self.into_transactions().filter_map(|transaction| match transaction {
            Transaction::Deploy(_, deployment, _) => Some(*deployment),
            _ => None,
        })
    }

    /// Returns a consuming iterator over all transactions in `self` that are executions.
    pub fn into_executions(self) -> impl Iterator<Item = Execution<N>> {
        self.into_transactions().filter_map(|transaction| match transaction {
            Transaction::Execute(_, execution, _) => Some(execution),
            _ => None,
        })
    }

    /// Returns a consuming iterator over all transitions.
    pub fn into_transitions(self) -> impl Iterator<Item = Transition<N>> {
        self.into_transactions().flat_map(Transaction::into_transitions)
    }

    /// Returns a consuming iterator over the transition IDs, for all transitions.
    pub fn into_transition_ids(self) -> impl Iterator<Item = N::TransitionID> {
        self.into_transactions().flat_map(Transaction::into_transition_ids)
    }

    /// Returns a consuming iterator over the transition public keys, for all transactions.
    pub fn into_transition_public_keys(self) -> impl Iterator<Item = Group<N>> {
        self.into_transactions().flat_map(Transaction::into_transition_public_keys)
    }

    /// Returns a consuming iterator over the origins, for all transition inputs that are records.
    pub fn into_origins(self) -> impl Iterator<Item = Origin<N>> {
        self.into_transitions().flat_map(Transition::into_origins)
    }

    /// Returns a consuming iterator over the tags, for all transition inputs that are records.
    pub fn into_tags(self) -> impl Iterator<Item = Field<N>> {
        self.into_transitions().flat_map(Transition::into_tags)
    }

    /// Returns a consuming iterator over the serial numbers, for all transition inputs that are records.
    pub fn into_serial_numbers(self) -> impl Iterator<Item = Field<N>> {
        self.into_transitions().flat_map(Transition::into_serial_numbers)
    }

    /// Returns a consuming iterator over the commitments, for all transition outputs that are records.
    pub fn into_commitments(self) -> impl Iterator<Item = Field<N>> {
        self.into_transitions().flat_map(Transition::into_commitments)
    }

    /// Returns a consuming iterator over the nonces, for all transition outputs that are records.
    pub fn into_nonces(self) -> impl Iterator<Item = Group<N>> {
        self.into_transitions().flat_map(Transition::into_nonces)
    }
}

impl<N: Network> Deref for Transactions<N> {
    type Target = IndexMap<N::TransactionID, Transaction<N>>;

    fn deref(&self) -> &Self::Target {
        &self.transactions
    }
}
