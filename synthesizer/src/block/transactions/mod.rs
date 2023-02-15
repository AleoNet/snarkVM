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

mod bytes;
mod merkle;
mod serialize;
mod string;

use crate::{
    block::{Transaction, Transition},
    process::{Deployment, Execution},
};
use console::{
    network::prelude::*,
    program::{Ciphertext, Record, TransactionsPath, TransactionsTree, TRANSACTIONS_DEPTH},
    types::{Field, Group},
};

use indexmap::IndexMap;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

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
    /// Returns `true` if the transactions contains the given transition ID.
    #[cfg(feature = "parallel")]
    pub fn contains_transition(&self, transition_id: &N::TransitionID) -> bool {
        self.par_values().any(|tx| tx.contains_transition(transition_id))
    }

    #[cfg(not(feature = "parallel"))]
    pub fn contains_transition(&self, transition_id: &N::TransitionID) -> bool {
        self.values().any(|tx| tx.contains_transition(transition_id))
    }

    /// Returns `true` if the transactions contains the given serial number.
    #[cfg(feature = "parallel")]
    pub fn contains_serial_number(&self, serial_number: &Field<N>) -> bool {
        self.par_values().any(|tx| tx.contains_serial_number(serial_number))
    }

    /// Returns `true` if the transactions contains the given serial number.
    #[cfg(not(feature = "parallel"))]
    pub fn contains_serial_number(&self, serial_number: &Field<N>) -> bool {
        self.values().any(|tx| tx.contains_serial_number(serial_number))
    }

    /// Returns `true` if the transactions contains the given commitment.
    #[cfg(feature = "parallel")]
    pub fn contains_commitment(&self, commitment: &Field<N>) -> bool {
        self.par_values().any(|tx| tx.contains_commitment(commitment))
    }

    /// Returns `true` if the transactions contains the given commitment.
    #[cfg(not(feature = "parallel"))]
    pub fn contains_commitment(&self, commitment: &Field<N>) -> bool {
        self.values().any(|tx| tx.contains_commitment(commitment))
    }
}

impl<N: Network> Transactions<N> {
    /// Returns the transaction with the given transition ID, if it exists.
    #[cfg(feature = "parallel")]
    pub fn find_transaction_for_transition_id(&self, transition_id: &N::TransitionID) -> Option<&Transaction<N>> {
        self.par_values().find_any(|tx| tx.contains_transition(transition_id))
    }

    /// Returns the transaction with the given transition ID, if it exists.
    #[cfg(not(feature = "parallel"))]
    pub fn find_transaction_for_transition_id(&self, transition_id: &N::TransitionID) -> Option<&Transaction<N>> {
        self.values().find(|tx| tx.contains_transition(transition_id))
    }

    /// Returns the transaction with the given serial number, if it exists.
    #[cfg(feature = "parallel")]
    pub fn find_transaction_for_serial_number(&self, serial_number: &Field<N>) -> Option<&Transaction<N>> {
        self.par_values().find_any(|tx| tx.contains_serial_number(serial_number))
    }

    /// Returns the transaction with the given serial number, if it exists.
    #[cfg(not(feature = "parallel"))]
    pub fn find_transaction_for_serial_number(&self, serial_number: &Field<N>) -> Option<&Transaction<N>> {
        self.values().find(|tx| tx.contains_serial_number(serial_number))
    }

    /// Returns the transaction with the given commitment, if it exists.
    #[cfg(feature = "parallel")]
    pub fn find_transaction_for_commitment(&self, commitment: &Field<N>) -> Option<&Transaction<N>> {
        self.par_values().find_any(|tx| tx.contains_commitment(commitment))
    }

    /// Returns the transaction with the given commitment, if it exists.
    #[cfg(not(feature = "parallel"))]
    pub fn find_transaction_for_commitment(&self, commitment: &Field<N>) -> Option<&Transaction<N>> {
        self.values().find(|tx| tx.contains_commitment(commitment))
    }

    /// Returns the transition with the corresponding transition ID, if it exists.
    #[cfg(feature = "parallel")]
    pub fn find_transition(&self, transition_id: &N::TransitionID) -> Option<&Transition<N>> {
        self.par_values().filter_map(|tx| tx.find_transition(transition_id)).find_any(|_| true)
    }

    /// Returns the transition with the corresponding transition ID, if it exists.
    #[cfg(not(feature = "parallel"))]
    pub fn find_transition(&self, transition_id: &N::TransitionID) -> Option<&Transition<N>> {
        self.values().find_map(|tx| tx.find_transition(transition_id))
    }

    /// Returns the transition for the given serial number, if it exists.
    #[cfg(feature = "parallel")]
    pub fn find_transition_for_serial_number(&self, serial_number: &Field<N>) -> Option<&Transition<N>> {
        self.par_values()
            .filter_map(|tx| tx.find_transition_for_serial_number(serial_number))
            .find_any(|_| true)
    }

    /// Returns the transition for the given serial number, if it exists.
    #[cfg(not(feature = "parallel"))]
    pub fn find_transition_for_serial_number(&self, serial_number: &Field<N>) -> Option<&Transition<N>> {
        self.values().find_map(|tx| tx.find_transition_for_serial_number(serial_number))
    }

    /// Returns the transition for the given commitment, if it exists.
    #[cfg(feature = "parallel")]
    pub fn find_transition_for_commitment(&self, commitment: &Field<N>) -> Option<&Transition<N>> {
        self.par_values().filter_map(|tx| tx.find_transition_for_commitment(commitment)).find_any(|_| true)
    }

    #[cfg(not(feature = "parallel"))]
    pub fn find_transition_for_commitment(&self, commitment: &Field<N>) -> Option<&Transition<N>> {
        self.values().find_map(|tx| tx.find_transition_for_commitment(commitment))
    }

    /// Returns the record with the corresponding commitment, if it exists.
    #[cfg(feature = "parallel")]
    pub fn find_record(&self, commitment: &Field<N>) -> Option<&Record<N, Ciphertext<N>>> {
        self.par_values().filter_map(|tx| tx.find_record(commitment)).find_any(|_| true)
    }

    /// Returns the record with the corresponding commitment, if it exists.
    #[cfg(not(feature = "parallel"))]
    pub fn find_record(&self, commitment: &Field<N>) -> Option<&Record<N, Ciphertext<N>>> {
        self.values().find_map(|tx| tx.find_record(commitment))
    }
}

impl<N: Network> Transactions<N> {
    /// The maximum number of transactions allowed in a block.
    pub const MAX_TRANSACTIONS: usize = usize::pow(2, TRANSACTIONS_DEPTH as u32);

    /// Returns an iterator over all transactions, for all transactions in `self`.
    pub fn iter(&self) -> impl '_ + Iterator<Item = &Transaction<N>> {
        self.transactions.values()
    }

    /// Returns an iterator over the transaction IDs, for all transactions in `self`.
    pub fn transaction_ids(&self) -> impl '_ + Iterator<Item = &N::TransactionID> {
        self.transactions.keys()
    }

    /// Returns an iterator over all transactions in `self` that are deployments.
    pub fn deployments(&self) -> impl '_ + Iterator<Item = &Deployment<N>> {
        self.iter().filter_map(|transaction| match transaction {
            Transaction::Deploy(_, deployment, _) => Some(deployment.as_ref()),
            _ => None,
        })
    }

    /// Returns an iterator over all transactions in `self` that are executions.
    pub fn executions(&self) -> impl '_ + Iterator<Item = &Execution<N>> {
        self.iter().filter_map(|transaction| match transaction {
            Transaction::Execute(_, execution, _) => Some(execution),
            _ => None,
        })
    }

    /// Returns an iterator over all transitions.
    pub fn transitions(&self) -> impl '_ + Iterator<Item = &Transition<N>> {
        self.iter().flat_map(Transaction::transitions)
    }

    /// Returns an iterator over the transition IDs, for all transitions.
    pub fn transition_ids(&self) -> impl '_ + Iterator<Item = &N::TransitionID> {
        self.iter().flat_map(Transaction::transition_ids)
    }

    /// Returns an iterator over the transition public keys, for all transactions.
    pub fn transition_public_keys(&self) -> impl '_ + Iterator<Item = &Group<N>> {
        self.iter().flat_map(Transaction::transition_public_keys)
    }

    /// Returns an iterator over the tags, for all transition inputs that are records.
    pub fn tags(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.iter().flat_map(Transaction::tags)
    }

    /// Returns an iterator over the serial numbers, for all transition inputs that are records.
    pub fn serial_numbers(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.iter().flat_map(Transaction::serial_numbers)
    }

    /// Returns an iterator over the commitments, for all transition outputs that are records.
    pub fn commitments(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.iter().flat_map(Transaction::commitments)
    }

    /// Returns an iterator over the records, for all transition outputs that are records.
    pub fn records(&self) -> impl '_ + Iterator<Item = (&Field<N>, &Record<N, Ciphertext<N>>)> {
        self.iter().flat_map(Transaction::records)
    }

    /// Returns an iterator over the nonces, for all transition outputs that are records.
    pub fn nonces(&self) -> impl '_ + Iterator<Item = &Group<N>> {
        self.iter().flat_map(Transaction::nonces)
    }

    /// Returns an iterator over the transaction fees, for all transactions.
    pub fn transaction_fees(&self) -> impl '_ + Iterator<Item = Result<i64>> {
        self.iter().map(Transaction::fee)
    }
}

impl<N: Network> IntoIterator for Transactions<N> {
    type IntoIter = indexmap::map::IntoValues<N::TransactionID, Self::Item>;
    type Item = Transaction<N>;

    /// Returns a consuming iterator over all transactions, for all transactions in `self`.
    fn into_iter(self) -> Self::IntoIter {
        self.transactions.into_values()
    }
}

impl<N: Network> Transactions<N> {
    /// Returns a consuming iterator over the transaction IDs, for all transactions in `self`.
    pub fn into_transaction_ids(self) -> impl Iterator<Item = N::TransactionID> {
        self.transactions.into_keys()
    }

    /// Returns a consuming iterator over all transactions in `self` that are deployments.
    pub fn into_deployments(self) -> impl Iterator<Item = Deployment<N>> {
        self.into_iter().filter_map(|transaction| match transaction {
            Transaction::Deploy(_, deployment, _) => Some(*deployment),
            _ => None,
        })
    }

    /// Returns a consuming iterator over all transactions in `self` that are executions.
    pub fn into_executions(self) -> impl Iterator<Item = Execution<N>> {
        self.into_iter().filter_map(|transaction| match transaction {
            Transaction::Execute(_, execution, _) => Some(execution),
            _ => None,
        })
    }

    /// Returns a consuming iterator over all transitions.
    pub fn into_transitions(self) -> impl Iterator<Item = Transition<N>> {
        self.into_iter().flat_map(Transaction::into_transitions)
    }

    /// Returns a consuming iterator over the transition IDs, for all transitions.
    pub fn into_transition_ids(self) -> impl Iterator<Item = N::TransitionID> {
        self.into_iter().flat_map(Transaction::into_transition_ids)
    }

    /// Returns a consuming iterator over the transition public keys, for all transactions.
    pub fn into_transition_public_keys(self) -> impl Iterator<Item = Group<N>> {
        self.into_iter().flat_map(Transaction::into_transition_public_keys)
    }

    /// Returns a consuming iterator over the tags, for all transition inputs that are records.
    pub fn into_tags(self) -> impl Iterator<Item = Field<N>> {
        self.into_iter().flat_map(Transaction::into_tags)
    }

    /// Returns a consuming iterator over the serial numbers, for all transition inputs that are records.
    pub fn into_serial_numbers(self) -> impl Iterator<Item = Field<N>> {
        self.into_iter().flat_map(Transaction::into_serial_numbers)
    }

    /// Returns a consuming iterator over the commitments, for all transition outputs that are records.
    pub fn into_commitments(self) -> impl Iterator<Item = Field<N>> {
        self.into_iter().flat_map(Transaction::into_commitments)
    }

    /// Returns a consuming iterator over the records, for all transition outputs that are records.
    pub fn into_records(self) -> impl Iterator<Item = (Field<N>, Record<N, Ciphertext<N>>)> {
        self.into_iter().flat_map(Transaction::into_records)
    }

    /// Returns a consuming iterator over the nonces, for all transition outputs that are records.
    pub fn into_nonces(self) -> impl Iterator<Item = Group<N>> {
        self.into_iter().flat_map(Transaction::into_nonces)
    }
}

impl<N: Network> Deref for Transactions<N> {
    type Target = IndexMap<N::TransactionID, Transaction<N>>;

    fn deref(&self) -> &Self::Target {
        &self.transactions
    }
}
