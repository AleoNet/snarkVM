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

impl<N: Network, B: BlockStorage<N>, T: TransactionStorage<N>> BlockStore<N, B, T> {
    /// Returns an iterator over all transactions.
    pub fn transactions(&self) -> impl '_ + Iterator<Item = Cow<'_, Transaction<N>>> {
        // TODO (raychu86): Make this utilized borrows and handle unwraps.
        self.transaction_ids().map(|tx_ids| match tx_ids {
            Cow::Borrowed(tx_id) => Cow::Owned(self.get_transaction(*tx_id).unwrap()),
            Cow::Owned(tx_id) => Cow::Owned(self.get_transaction(tx_id.to_owned()).unwrap()),
        })
    }

    /// Returns an iterator over the transaction IDs, for all transactions in `self`.
    pub fn transaction_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, N::TransactionID>> {
        self.transactions.values().flat_map(|tx_ids| match tx_ids {
            Cow::Borrowed(tx_ids) => tx_ids.iter().map(Cow::Borrowed).collect::<Vec<_>>(),
            Cow::Owned(tx_ids) => {
                tx_ids.to_owned().iter().map(|tx_id| Cow::Owned(tx_id.to_owned())).collect::<Vec<_>>()
            }
        })
    }

    /// Returns an iterator over all transactions in `self` that are deployments.
    pub fn deployments(&self) -> impl '_ + Iterator<Item = Cow<'_, Deployment<N>>> {
        self.transaction_store.deployments()
    }

    // TODO (raychu86): Implement iterators for executions.
    // /// Returns an iterator over all transactions in `self` that are executions.
    // pub fn executions(&self) -> impl '_ + Iterator<Item = Cow<'_, Execution<N>>> {
    //     self.transaction_store.executions()
    // }

    /// Returns an iterator over all executed transitions.
    pub fn transitions(&self) -> impl '_ + Iterator<Item = Cow<'_, Transition<N>>> {
        self.transaction_store.transitions()
    }

    /// Returns an iterator over the transition IDs, for all executed transitions.
    pub fn transition_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, N::TransitionID>> {
        self.transaction_store.transition_ids()
    }

    /// Returns an iterator over the transition public keys, for all executed transactions.
    pub fn transition_public_keys(&self) -> impl '_ + Iterator<Item = Cow<'_, Group<N>>> {
        self.transaction_store.transition_public_keys()
    }

    /// Returns an iterator over the serial numbers, for all executed transition inputs that are records.
    pub fn serial_numbers(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.transaction_store.serial_numbers()
    }

    /// Returns an iterator over the commitments, for all executed transition outputs that are records.
    pub fn commitments(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.transaction_store.commitments()
    }

    /// Returns an iterator over the nonces, for all executed transition outputs that are records.
    pub fn nonces(&self) -> impl '_ + Iterator<Item = Cow<'_, Group<N>>> {
        self.transaction_store.nonces()
    }
}
