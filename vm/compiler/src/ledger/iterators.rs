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

/// A wrapper enum able to contain and iterate over two `Cow` iterators of different types.
enum CowIter<'a, T: 'a + Clone, I1: Iterator<Item = &'a T>, I2: Iterator<Item = T>> {
    Borrowed(I1),
    Owned(I2),
}

impl<'a, T: 'a + Clone, I1: Iterator<Item = &'a T>, I2: Iterator<Item = T>> Iterator for CowIter<'a, T, I1, I2> {
    type Item = Cow<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Borrowed(iter) => Some(Cow::Borrowed(iter.next()?)),
            Self::Owned(iter) => Some(Cow::Owned(iter.next()?)),
        }
    }
}

macro_rules! transactions_iterator {
    ($self:expr, $method:ident) => {
        paste::paste! {
            $self.transactions.values().flat_map(|tx| match tx {
                Cow::Borrowed(tx) => CowIter::Borrowed(Transactions::$method(tx)),
                Cow::Owned(tx) => CowIter::Owned(Transactions::[<into_ $method>](tx)),
            })
        }
    };
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
        transactions_iterator!(self, transactions)
    }

    /// Returns an iterator over the transaction IDs, for all transactions in `self`.
    pub fn transaction_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, N::TransactionID>> {
        transactions_iterator!(self, transaction_ids)
    }

    /// Returns an iterator over all transactions in `self` that are deployments.
    pub fn deployments(&self) -> impl '_ + Iterator<Item = Cow<'_, Deployment<N>>> {
        transactions_iterator!(self, deployments)
    }

    /// Returns an iterator over all transactions in `self` that are executions.
    pub fn executions(&self) -> impl '_ + Iterator<Item = Cow<'_, Execution<N>>> {
        transactions_iterator!(self, executions)
    }

    /// Returns an iterator over all transitions.
    pub fn transitions(&self) -> impl '_ + Iterator<Item = Cow<'_, Transition<N>>> {
        transactions_iterator!(self, transitions)
    }

    /// Returns an iterator over the transition IDs, for all transitions.
    pub fn transition_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, N::TransitionID>> {
        transactions_iterator!(self, transition_ids)
    }

    /// Returns an iterator over the transition public keys, for all transactions.
    pub fn transition_public_keys(&self) -> impl '_ + Iterator<Item = Cow<'_, Group<N>>> {
        transactions_iterator!(self, transition_public_keys)
    }

    /// Returns an iterator over the tags, for all transition inputs that are records.
    pub fn tags(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        transactions_iterator!(self, tags)
    }

    /// Returns an iterator over the serial numbers, for all transition inputs that are records.
    pub fn serial_numbers(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        transactions_iterator!(self, serial_numbers)
    }

    /// Returns an iterator over the commitments, for all transition outputs that are records.
    pub fn commitments(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        transactions_iterator!(self, commitments)
    }

    /// Returns an iterator over the nonces, for all transition outputs that are records.
    pub fn nonces(&self) -> impl '_ + Iterator<Item = Cow<'_, Group<N>>> {
        transactions_iterator!(self, nonces)
    }
}
