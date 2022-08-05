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

impl<
    N: Network,
    DeploymentsMap: for<'a> Map<'a, N::TransactionID, (Deployment<N>, N::TransitionID)>,
    ExecutionsMap: for<'a> Map<'a, N::TransactionID, (Vec<N::TransitionID>, Option<N::TransitionID>)>,
    TransitionsMap: for<'a> Map<'a, N::TransitionID, Transition<N>>,
    TransitionPublicKeysMap: for<'a> Map<'a, Group<N>, N::TransitionID>,
    SerialNumbersMap: for<'a> Map<'a, Field<N>, N::TransitionID>,
    CommitmentsMap: for<'a> Map<'a, Field<N>, N::TransitionID>,
    OriginsMap: for<'a> Map<'a, Origin<N>, N::TransitionID>,
    NonceMap: for<'a> Map<'a, Group<N>, N::TransitionID>,
>
    TransactionStore<
        N,
        DeploymentsMap,
        ExecutionsMap,
        TransitionsMap,
        TransitionPublicKeysMap,
        SerialNumbersMap,
        CommitmentsMap,
        OriginsMap,
        NonceMap,
    >
{
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

    // TODO (raychu86): Impelement iterators for executions.
    // /// Returns an iterator over all transactions in `self` that are executions.
    // pub fn executions(&self) -> impl '_ + Iterator<Item = Cow<'_, Execution<N>>> {
    //
    // }

    /// Returns an iterator over all executed transitions.
    pub fn transitions(&self) -> impl '_ + Iterator<Item = Cow<'_, Transition<N>>> {
        self.transitions.values()
    }

    /// Returns an iterator over the transition IDs, for all executed transitions.
    pub fn transition_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, N::TransitionID>> {
        self.transitions.keys()
    }

    /// Returns an iterator over the transition public keys, for all executed transactions.
    pub fn transition_public_keys(&self) -> impl '_ + Iterator<Item = Cow<'_, Group<N>>> {
        self.transition_public_keys.keys()
    }

    /// Returns an iterator over the serial numbers, for all executed transition inputs that are records.
    pub fn serial_numbers(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.serial_numbers.keys()
    }

    /// Returns an iterator over the commitments, for all executed transition outputs that are records.
    pub fn commitments(&self) -> impl '_ + Iterator<Item = Cow<'_, Field<N>>> {
        self.commitments.keys()
    }

    /// Returns an iterator over the origins, for all executed transition inputs that are records.
    pub fn origins(&self) -> impl '_ + Iterator<Item = Cow<'_, Origin<N>>> {
        self.origins.keys()
    }

    /// Returns an iterator over the nonces, for all executed transition outputs that are records.
    pub fn nonces(&self) -> impl '_ + Iterator<Item = Cow<'_, Group<N>>> {
        self.nonces.keys()
    }
}
