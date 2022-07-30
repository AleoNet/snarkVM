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

impl<
    N: Network,
    PreviousHashesMap: for<'a> Map<'a, u32, N::BlockHash>,
    HeadersMap: for<'a> Map<'a, u32, Header<N>>,
    TransactionsMap: for<'a> Map<'a, u32, Transactions<N>>,
    ProgramsMap: for<'a> Map<'a, ProgramID<N>, Deployment<N>>,
> Ledger<N, PreviousHashesMap, HeadersMap, TransactionsMap, ProgramsMap>
{
    /// Returns an iterator over all transactions.
    pub fn transactions(&self) -> impl '_ + Iterator<Item = &Transaction<N>> {
        self.transactions.values().flat_map(Transactions::transactions)
    }

    /// Returns an iterator over the transaction IDs, for all transactions in `self`.
    pub fn transaction_ids(&self) -> impl '_ + Iterator<Item = &N::TransactionID> {
        self.transactions.values().flat_map(Transactions::transaction_ids)
    }

    /// Returns an iterator over all transactions in `self` that are deployments.
    pub fn deployments(&self) -> impl '_ + Iterator<Item = &Deployment<N>> {
        self.transactions.values().flat_map(Transactions::deployments)
    }

    /// Returns an iterator over all transactions in `self` that are executions.
    pub fn executions(&self) -> impl '_ + Iterator<Item = &Execution<N>> {
        self.transactions.values().flat_map(Transactions::executions)
    }

    /// Returns an iterator over all executed transitions.
    pub fn transitions(&self) -> impl '_ + Iterator<Item = &Transition<N>> {
        self.transactions.values().flat_map(Transactions::transitions)
    }

    /// Returns an iterator over the transition IDs, for all executed transitions.
    pub fn transition_ids(&self) -> impl '_ + Iterator<Item = &N::TransitionID> {
        self.transactions.values().flat_map(Transactions::transition_ids)
    }

    /// Returns an iterator over the transition public keys, for all executed transactions.
    pub fn transition_public_keys(&self) -> impl '_ + Iterator<Item = &Group<N>> {
        self.transactions.values().flat_map(Transactions::transition_public_keys)
    }

    /// Returns an iterator over the serial numbers, for all executed transition inputs that are records.
    pub fn serial_numbers(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.values().flat_map(Transactions::serial_numbers)
    }

    /// Returns an iterator over the commitments, for all executed transition outputs that are records.
    pub fn commitments(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.values().flat_map(Transactions::commitments)
    }

    /// Returns an iterator over the nonces, for all executed transition outputs that are records.
    pub fn nonces(&self) -> impl '_ + Iterator<Item = &Group<N>> {
        self.transactions.values().flat_map(Transactions::nonces)
    }
}
