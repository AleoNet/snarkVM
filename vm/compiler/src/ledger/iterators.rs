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
use std::borrow::Cow;

// A wrapper object able to contain and iterate over two `Cow` iterators of different types.
enum IterWrap<'a, T: 'a + Clone, I1: Iterator<Item = &'a T>, I2: Iterator<Item = T>> {
    Borrowed(I1),
    Owned(I2),
}

impl<'a, T: 'a + Clone, I1: Iterator<Item = &'a T>, I2: Iterator<Item = T>> Iterator for IterWrap<'a, T, I1, I2> {
    type Item = Cow<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Borrowed(iter) => Some(Cow::Borrowed(iter.next()?)),
            Self::Owned(iter) => Some(Cow::Owned(iter.next()?)),
        }
    }
}

impl<
    N: Network,
    PreviousHashesMap: for<'a> Map<'a, u32, N::BlockHash>,
    HeadersMap: for<'a> Map<'a, u32, Header<N>>,
    TransactionsMap: for<'a> Map<'a, u32, Transactions<N>>,
    SignatureMap: for<'a> Map<'a, u32, Signature<N>>,
> Ledger<N, PreviousHashesMap, HeadersMap, TransactionsMap, SignatureMap>
{
    /// Returns an iterator over all transactions.
    pub fn transactions(&self) -> impl '_ + Iterator<Item = Cow<'_, Transaction<N>>> {
        self.transactions.values().flat_map(|ts| match ts {
            Cow::Borrowed(ts) => IterWrap::Borrowed(Transactions::transactions(ts)),
            Cow::Owned(ts) => IterWrap::Owned(Transactions::into_transactions(ts)),
        })
    }

    /// Returns an iterator over the transaction IDs, for all transactions in `self`.
    pub fn transaction_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, N::TransactionID>> {
        self.transactions.values().flat_map(|ts| match ts {
            Cow::Borrowed(ts) => IterWrap::Borrowed(Transactions::transaction_ids(ts)),
            Cow::Owned(ts) => IterWrap::Owned(Transactions::into_transaction_ids(ts)),
        })
    }

    /// Returns an iterator over all transactions in `self` that are deployments.
    pub fn deployments(&self) -> impl '_ + Iterator<Item = Cow<'_, Deployment<N>>> {
        self.transactions.values().flat_map(|ts| match ts {
            Cow::Borrowed(ts) => IterWrap::Borrowed(Transactions::deployments(ts)),
            Cow::Owned(ts) => IterWrap::Owned(Transactions::into_deployments(ts)),
        })
    }

    /// Returns an iterator over all transactions in `self` that are executions.
    pub fn executions(&self) -> impl '_ + Iterator<Item = Cow<'_, Execution<N>>> {
        self.transactions.values().flat_map(|ts| match ts {
            Cow::Borrowed(ts) => IterWrap::Borrowed(Transactions::executions(ts)),
            Cow::Owned(ts) => IterWrap::Owned(Transactions::into_executions(ts)),
        })
    }

    /// Returns an iterator over all executed transitions.
    pub fn transitions(&self) -> impl '_ + Iterator<Item = Cow<'_, Transition<N>>> {
        self.transactions.values().flat_map(|ts| match ts {
            Cow::Borrowed(ts) => IterWrap::Borrowed(Transactions::transitions(ts)),
            Cow::Owned(ts) => IterWrap::Owned(Transactions::into_transitions(ts)),
        })
    }

    /// Returns an iterator over the transition IDs, for all executed transitions.
    pub fn transition_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, N::TransitionID>> {
        self.transactions.values().flat_map(|ts| match ts {
            Cow::Borrowed(ts) => IterWrap::Borrowed(Transactions::transition_ids(ts)),
            Cow::Owned(ts) => IterWrap::Owned(Transactions::into_transition_ids(ts)),
        })
    }

    /// Returns an iterator over the transition public keys, for all executed transactions.
    pub fn transition_public_keys(&self) -> impl '_ + Iterator<Item = Cow<'_, Group<N>>> {
        self.transactions.values().flat_map(|ts| match ts {
            Cow::Borrowed(ts) => IterWrap::Borrowed(Transactions::transition_public_keys(ts)),
            Cow::Owned(ts) => IterWrap::Owned(Transactions::into_transition_public_keys(ts)),
        })
    }

    /// Returns an iterator over the serial numbers, for all executed transition inputs that are records.
    pub fn serial_numbers(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.transactions.values().flat_map(|ts| match ts {
            Cow::Borrowed(ts) => IterWrap::Borrowed(Transactions::serial_numbers(ts)),
            Cow::Owned(ts) => IterWrap::Owned(Transactions::into_serial_numbers(ts)),
        })
    }

    /// Returns an iterator over the commitments, for all executed transition outputs that are records.
    pub fn commitments(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.transactions.values().flat_map(|ts| match ts {
            Cow::Borrowed(ts) => IterWrap::Borrowed(Transactions::commitments(ts)),
            Cow::Owned(ts) => IterWrap::Owned(Transactions::into_commitments(ts)),
        })
    }

    /// Returns an iterator over the nonces, for all executed transition outputs that are records.
    pub fn nonces(&self) -> impl '_ + Iterator<Item = Cow<'_, Group<N>>> {
        self.transactions.values().flat_map(|ts| match ts {
            Cow::Borrowed(ts) => IterWrap::Borrowed(Transactions::nonces(ts)),
            Cow::Owned(ts) => IterWrap::Owned(Transactions::into_nonces(ts)),
        })
    }
}
