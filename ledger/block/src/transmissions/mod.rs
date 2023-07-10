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

mod bytes;
mod serialize;
mod string;

use crate::{CoinbaseSolution, ConfirmedTransaction, PuzzleCommitment, Ratify, Transaction, Transactions, Transition};
use console::{
    network::prelude::*,
    program::{Ciphertext, Record},
    types::{Field, Group, U64},
};

/// the transmissions included in the block.
#[derive(Clone, PartialEq, Eq)]
pub struct Transmissions<N: Network> {
    /// The transactions in this block.
    transactions: Transactions<N>,
    /// The ratifications in this block.
    ratifications: Vec<Ratify<N>>,
    /// The coinbase solution.
    coinbase: Option<CoinbaseSolution<N>>,
}

impl<N: Network> Transmissions<N> {
    /// Initializes a new instance of `Transmissions`.
    pub fn from(
        transactions: Transactions<N>,
        ratifications: Vec<Ratify<N>>,
        coinbase: Option<CoinbaseSolution<N>>,
    ) -> Self {
        Self { transactions, ratifications, coinbase }
    }

    /// Returns the transactions.
    pub const fn transactions(&self) -> &Transactions<N> {
        &self.transactions
    }

    /// Returns the ratifications.
    pub const fn ratifications(&self) -> &Vec<Ratify<N>> {
        &self.ratifications
    }

    /// Returns the coinbase solution.
    pub const fn coinbase(&self) -> Option<&CoinbaseSolution<N>> {
        self.coinbase.as_ref()
    }
}

impl<N: Network> Transmissions<N> {
    /// Returns `true` if the transmissions contains the given transition ID.
    pub fn contains_transition(&self, transition_id: &N::TransitionID) -> bool {
        self.transactions.contains_transition(transition_id)
    }

    /// Returns `true` if the transmissions contains the given serial number.
    pub fn contains_serial_number(&self, serial_number: &Field<N>) -> bool {
        self.transactions.contains_serial_number(serial_number)
    }

    /// Returns `true` if the transmissions contains the given commitment.
    pub fn contains_commitment(&self, commitment: &Field<N>) -> bool {
        self.transactions.contains_commitment(commitment)
    }
}

impl<N: Network> Transmissions<N> {
    /// Returns the transaction with the given transition ID, if it exists.
    pub fn find_transaction_for_transition_id(&self, transition_id: &N::TransitionID) -> Option<&Transaction<N>> {
        self.transactions.find_transaction_for_transition_id(transition_id)
    }

    /// Returns the transaction with the given serial number, if it exists.
    pub fn find_transaction_for_serial_number(&self, serial_number: &Field<N>) -> Option<&Transaction<N>> {
        self.transactions.find_transaction_for_serial_number(serial_number)
    }

    /// Returns the transaction with the given commitment, if it exists.
    pub fn find_transaction_for_commitment(&self, commitment: &Field<N>) -> Option<&Transaction<N>> {
        self.transactions.find_transaction_for_commitment(commitment)
    }

    /// Returns the transition with the corresponding transition ID, if it exists.
    pub fn find_transition(&self, transition_id: &N::TransitionID) -> Option<&Transition<N>> {
        self.transactions.find_transition(transition_id)
    }

    /// Returns the transition for the given serial number, if it exists.
    pub fn find_transition_for_serial_number(&self, serial_number: &Field<N>) -> Option<&Transition<N>> {
        self.transactions.find_transition_for_serial_number(serial_number)
    }

    /// Returns the transition for the given commitment, if it exists.
    pub fn find_transition_for_commitment(&self, commitment: &Field<N>) -> Option<&Transition<N>> {
        self.transactions.find_transition_for_commitment(commitment)
    }

    /// Returns the record with the corresponding commitment, if it exists.
    pub fn find_record(&self, commitment: &Field<N>) -> Option<&Record<N, Ciphertext<N>>> {
        self.transactions.find_record(commitment)
    }
}

impl<N: Network> Transmissions<N> {
    /// Returns the puzzle commitments in the transmissions.
    pub fn puzzle_commitments(&self) -> Option<impl '_ + Iterator<Item = PuzzleCommitment<N>>> {
        self.coinbase.as_ref().map(|solution| solution.puzzle_commitments())
    }

    /// Returns an iterator over the transaction IDs, for all transactions in `self`.
    pub fn transaction_ids(&self) -> impl '_ + Iterator<Item = &N::TransactionID> {
        self.transactions.transaction_ids()
    }

    /// Returns an iterator over all transactions in `self` that are accepted deploy transactions.
    pub fn deployments(&self) -> impl '_ + Iterator<Item = &ConfirmedTransaction<N>> {
        self.transactions.deployments()
    }

    /// Returns an iterator over all transactions in `self` that are accepted execute transactions.
    pub fn executions(&self) -> impl '_ + Iterator<Item = &ConfirmedTransaction<N>> {
        self.transactions.executions()
    }

    /// Returns an iterator over all transitions.
    pub fn transitions(&self) -> impl '_ + Iterator<Item = &Transition<N>> {
        self.transactions.transitions()
    }

    /// Returns an iterator over the transition IDs, for all transitions.
    pub fn transition_ids(&self) -> impl '_ + Iterator<Item = &N::TransitionID> {
        self.transactions.transition_ids()
    }

    /// Returns an iterator over the transition public keys, for all transactions.
    pub fn transition_public_keys(&self) -> impl '_ + Iterator<Item = &Group<N>> {
        self.transactions.transition_public_keys()
    }

    /// Returns an iterator over the transition commitments, for all transactions.
    pub fn transition_commitments(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.transition_commitments()
    }

    /// Returns an iterator over the tags, for all transition inputs that are records.
    pub fn tags(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.tags()
    }

    /// Returns an iterator over the input IDs, for all transition inputs that are records.
    pub fn input_ids(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.input_ids()
    }

    /// Returns an iterator over the serial numbers, for all transition inputs that are records.
    pub fn serial_numbers(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.serial_numbers()
    }

    /// Returns an iterator over the output IDs, for all transition inputs that are records.
    pub fn output_ids(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.output_ids()
    }

    /// Returns an iterator over the commitments, for all transition outputs that are records.
    pub fn commitments(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.commitments()
    }

    /// Returns an iterator over the records, for all transition outputs that are records.
    pub fn records(&self) -> impl '_ + Iterator<Item = (&Field<N>, &Record<N, Ciphertext<N>>)> {
        self.transactions.records()
    }

    /// Returns an iterator over the nonces, for all transition outputs that are records.
    pub fn nonces(&self) -> impl '_ + Iterator<Item = &Group<N>> {
        self.transactions.nonces()
    }

    /// Returns an iterator over the transaction fees, for all transactions.
    pub fn transaction_fees(&self) -> impl '_ + Iterator<Item = Result<U64<N>>> {
        self.transactions.transaction_fees()
    }
}

impl<N: Network> Transmissions<N> {
    /// Returns a consuming iterator over the transaction IDs, for all transactions in `self`.
    pub fn into_transaction_ids(self) -> impl Iterator<Item = N::TransactionID> {
        self.transactions.into_transaction_ids()
    }

    /// Returns a consuming iterator over all transactions in `self` that are accepted deploy transactions.
    pub fn into_deployments(self) -> impl Iterator<Item = ConfirmedTransaction<N>> {
        self.transactions.into_deployments()
    }

    /// Returns a consuming iterator over all transactions in `self` that are accepted execute transactions.
    pub fn into_executions(self) -> impl Iterator<Item = ConfirmedTransaction<N>> {
        self.transactions.into_executions()
    }

    /// Returns a consuming iterator over all transitions.
    pub fn into_transitions(self) -> impl Iterator<Item = Transition<N>> {
        self.transactions.into_transitions()
    }

    /// Returns a consuming iterator over the transition IDs, for all transitions.
    pub fn into_transition_ids(self) -> impl Iterator<Item = N::TransitionID> {
        self.transactions.into_transition_ids()
    }

    /// Returns a consuming iterator over the transition public keys, for all transactions.
    pub fn into_transition_public_keys(self) -> impl Iterator<Item = Group<N>> {
        self.transactions.into_transition_public_keys()
    }

    /// Returns a consuming iterator over the tags, for all transition inputs that are records.
    pub fn into_tags(self) -> impl Iterator<Item = Field<N>> {
        self.transactions.into_tags()
    }

    /// Returns a consuming iterator over the serial numbers, for all transition inputs that are records.
    pub fn into_serial_numbers(self) -> impl Iterator<Item = Field<N>> {
        self.transactions.into_serial_numbers()
    }

    /// Returns a consuming iterator over the commitments, for all transition outputs that are records.
    pub fn into_commitments(self) -> impl Iterator<Item = Field<N>> {
        self.transactions.into_commitments()
    }

    /// Returns a consuming iterator over the records, for all transition outputs that are records.
    pub fn into_records(self) -> impl Iterator<Item = (Field<N>, Record<N, Ciphertext<N>>)> {
        self.transactions.into_records()
    }

    /// Returns a consuming iterator over the nonces, for all transition outputs that are records.
    pub fn into_nonces(self) -> impl Iterator<Item = Group<N>> {
        self.transactions.into_nonces()
    }
}

#[cfg(test)]
pub mod test_helpers {
    use super::*;

    type CurrentNetwork = console::network::Testnet3;

    /// Samples a block transmissions.
    pub(crate) fn sample_transmissions(rng: &mut TestRng) -> Transmissions<CurrentNetwork> {
        // Sample the transactions.
        let transactions = crate::transactions::test_helpers::sample_block_transactions(rng);

        // Sample the ratifications.
        let ratify = crate::ratify::test_helpers::sample_ratify_objects(rng);

        // Sample the coinbase.
        let coinbase = crate::test_helpers::sample_genesis_block(rng).coinbase().cloned();

        Transmissions::from(transactions, ratify, coinbase)
    }
}
