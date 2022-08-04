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
    ledger::{Block, Deployment, Header, Origin, Transaction, Transition},
    memory_map::MemoryMap,
    Map,
    MapReader,
};

use console::{
    network::prelude::*,
    types::{Field, Group},
};

use anyhow::Result;
use std::marker::PhantomData;

/// The transaction state stored in a ledger.
/// `PublicKeysMap`, `SerialNumbersMap`, `CommitmentsMap`, `OriginsMap`, and `NonceMap` store redundant data for faster lookup.
#[derive(Clone)]
pub struct TransactionStore<
    N: Network,
    DeploymentsMap: for<'a> Map<'a, N::TransactionID, (Deployment<N>, N::TransitionID)>,
    ExecutionsMap: for<'a> Map<'a, N::TransactionID, (Vec<N::TransitionID>, Option<N::TransitionID>)>,
    TransitionsMap: for<'a> Map<'a, N::TransitionID, Transition<N>>,
    PublicKeysMap: for<'a> Map<'a, Group<N>, N::TransitionID>,
    SerialNumbersMap: for<'a> Map<'a, Field<N>, N::TransitionID>,
    CommitmentsMap: for<'a> Map<'a, Field<N>, N::TransitionID>,
    OriginsMap: for<'a> Map<'a, Field<N>, N::TransitionID>,
    NonceMap: for<'a> Map<'a, Group<N>, N::TransitionID>,
> {
    /// The map of program deployments.
    deployments: DeploymentsMap,
    /// The map of program executions.
    executions: ExecutionsMap,
    /// The map of transitions.
    transitions: TransitionsMap,
    /// The map of serial numbers.
    public_keys: PublicKeysMap,
    /// The map of serial numbers.
    serial_numbers: SerialNumbersMap,
    /// The map of commitments.
    commitments: CommitmentsMap,
    /// The map of origins.
    origins: OriginsMap,
    /// The map of nonces.
    nonces: NonceMap,
    /// PhantomData.
    _network: PhantomData<N>,
}

impl<N: Network>
    TransactionStore<
        N,
        MemoryMap<N::TransactionID, (Deployment<N>, N::TransitionID)>,
        MemoryMap<N::TransactionID, (Vec<N::TransitionID>, Option<N::TransitionID>)>,
        MemoryMap<N::TransitionID, Transition<N>>,
        MemoryMap<Group<N>, N::TransitionID>,
        MemoryMap<Field<N>, N::TransitionID>,
        MemoryMap<Field<N>, N::TransitionID>,
        MemoryMap<Field<N>, N::TransitionID>,
        MemoryMap<Group<N>, N::TransitionID>,
    >
{
    /// Initializes a new instance of `TransactionStore`.
    pub fn new() -> Self {
        Self {
            deployments: Default::default(),
            executions: Default::default(),
            transitions: Default::default(),
            public_keys: Default::default(),
            serial_numbers: Default::default(),
            commitments: Default::default(),
            origins: Default::default(),
            nonces: Default::default(),
            _network: PhantomData,
        }
    }
}

impl<
    N: Network,
    DeploymentsMap: for<'a> Map<'a, N::TransactionID, (Deployment<N>, N::TransitionID)>,
    ExecutionsMap: for<'a> Map<'a, N::TransactionID, (Vec<N::TransitionID>, Option<N::TransitionID>)>,
    TransitionsMap: for<'a> Map<'a, N::TransitionID, Transition<N>>,
    PublicKeysMap: for<'a> Map<'a, Group<N>, N::TransitionID>,
    SerialNumbersMap: for<'a> Map<'a, Field<N>, N::TransitionID>,
    CommitmentsMap: for<'a> Map<'a, Field<N>, N::TransitionID>,
    OriginsMap: for<'a> Map<'a, Field<N>, N::TransitionID>,
    NonceMap: for<'a> Map<'a, Group<N>, N::TransitionID>,
>
    TransactionStore<
        N,
        DeploymentsMap,
        ExecutionsMap,
        TransitionsMap,
        PublicKeysMap,
        SerialNumbersMap,
        CommitmentsMap,
        OriginsMap,
        NonceMap,
    >
{
    /// Initializes a new instance of `TransactionStore` from the given maps.
    pub fn from_maps(
        deployments: DeploymentsMap,
        executions: ExecutionsMap,
        transitions: TransitionsMap,
        public_keys: PublicKeysMap,
        serial_numbers: SerialNumbersMap,
        commitments: CommitmentsMap,
        origins: OriginsMap,
        nonces: NonceMap,
    ) -> Result<Self> {
        let transaction_store = Self {
            deployments,
            executions,
            transitions,
            public_keys,
            serial_numbers,
            commitments,
            origins,
            nonces,
            _network: PhantomData,
        };

        // TODO (raychu86): Enforce that all the transaction state is valid.

        Ok(transaction_store)
    }

    /// Checks the given transaction is well formed and unique.
    pub fn check_transaction(&self, transaction: Transaction<N>) -> Result<()> {
        // TODO (raychu86): Check that the transaction is valid.

        Ok(())
    }

    /// Adds the given transaction to the transaction store.
    pub fn insert(&mut self, transaction: Transaction<N>) -> Result<Self> {
        // TODO (raychu86): Enforce that all the transaction state is valid.

        unimplemented!()
    }
}
