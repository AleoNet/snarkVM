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

use crate::store::{
    BlockMemory,
    BlockStorage,
    BlockStore,
    ProgramMemory,
    ProgramStorage,
    ProgramStore,
    TransactionMemory,
    TransactionStorage,
    TransactionStore,
    TransitionMemory,
    TransitionStorage,
    TransitionStore,
};
use console::network::prelude::*;

use anyhow::Result;
use core::marker::PhantomData;

/// A trait for consensus storage.
pub trait ConsensusStorage<N: Network>: 'static + Clone + Send + Sync {
    /// The program storage.
    type ProgramStorage: ProgramStorage<N>;
    /// The block storage.
    type BlockStorage: BlockStorage<
        N,
        TransactionStorage = Self::TransactionStorage,
        TransitionStorage = Self::TransitionStorage,
    >;
    /// The transaction storage.
    type TransactionStorage: TransactionStorage<N, TransitionStorage = Self::TransitionStorage>;
    /// The transition storage.
    type TransitionStorage: TransitionStorage<N>;

    /// Initializes the consensus storage.
    fn open(dev: Option<u16>) -> Result<Self>;

    /// Returns the program storage.
    fn program_store(&self) -> &ProgramStore<N, Self::ProgramStorage>;
    /// Returns the block storage.
    fn block_store(&self) -> &BlockStore<N, Self::BlockStorage>;
    /// Returns the transaction store.
    fn transaction_store(&self) -> &TransactionStore<N, Self::TransactionStorage> {
        self.block_store().transaction_store()
    }
    /// Returns the transition store.
    fn transition_store(&self) -> &TransitionStore<N, Self::TransitionStorage> {
        self.block_store().transition_store()
    }
    /// Returns the optional development ID.
    fn dev(&self) -> Option<u16> {
        debug_assert!(self.block_store().dev() == self.transaction_store().dev());
        debug_assert!(self.transaction_store().dev() == self.transition_store().dev());
        self.transition_store().dev()
    }

    /// Starts an atomic batch write operation.
    fn start_atomic(&self) {
        self.program_store().start_atomic();
        self.block_store().start_atomic();
    }

    /// Checks if an atomic batch is in progress.
    fn is_atomic_in_progress(&self) -> bool {
        self.program_store().is_atomic_in_progress() || self.block_store().is_atomic_in_progress()
    }

    /// Aborts an atomic batch write operation.
    fn abort_atomic(&self) {
        self.program_store().abort_atomic();
        self.block_store().abort_atomic();
    }

    /// Finishes an atomic batch write operation.
    fn finish_atomic(&self) -> Result<()> {
        self.program_store().finish_atomic()?;
        self.block_store().finish_atomic()
    }
}

/// An in-memory consensus storage.
#[derive(Clone)]
pub struct ConsensusMemory<N: Network> {
    /// The program store.
    program_store: ProgramStore<N, ProgramMemory<N>>,
    /// The block store.
    block_store: BlockStore<N, BlockMemory<N>>,
}

#[rustfmt::skip]
impl<N: Network> ConsensusStorage<N> for ConsensusMemory<N> {
    type ProgramStorage = ProgramMemory<N>;
    type BlockStorage = BlockMemory<N>;
    type TransactionStorage = TransactionMemory<N>;
    type TransitionStorage = TransitionMemory<N>;

    /// Initializes the consensus storage.
    fn open(dev: Option<u16>) -> Result<Self> {
        // Initialize the program store.
        let program_store = ProgramStore::<N, ProgramMemory<N>>::open(dev)?;
        // Initialize the block store.
        let block_store = BlockStore::<N, BlockMemory<N>>::open(dev)?;
        // Return the consensus storage.
        Ok(Self {
            program_store,
            block_store,
        })
    }

    /// Returns the program store.
    fn program_store(&self) -> &ProgramStore<N, Self::ProgramStorage> {
        &self.program_store
    }

    /// Returns the block store.
    fn block_store(&self) -> &BlockStore<N, Self::BlockStorage> {
        &self.block_store
    }
}

/// The consensus store.
#[derive(Clone)]
pub struct ConsensusStore<N: Network, C: ConsensusStorage<N>> {
    /// The consensus storage.
    storage: C,
    /// PhantomData.
    _phantom: PhantomData<N>,
}

impl<N: Network, C: ConsensusStorage<N>> ConsensusStore<N, C> {
    /// Initializes the consensus store.
    pub fn open(dev: Option<u16>) -> Result<Self> {
        // Initialize the consensus storage.
        let storage = C::open(dev)?;
        // Return the consensus store.
        Ok(Self { storage, _phantom: PhantomData })
    }

    /// Initializes a consensus store from storage.
    pub fn from(storage: C) -> Self {
        Self { storage, _phantom: PhantomData }
    }

    /// Returns the program store.
    pub fn program_store(&self) -> &ProgramStore<N, C::ProgramStorage> {
        self.storage.program_store()
    }

    /// Returns the block store.
    pub fn block_store(&self) -> &BlockStore<N, C::BlockStorage> {
        self.storage.block_store()
    }

    /// Returns the transaction store.
    pub fn transaction_store(&self) -> &TransactionStore<N, C::TransactionStorage> {
        self.storage.transaction_store()
    }

    /// Returns the transition store.
    pub fn transition_store(&self) -> &TransitionStore<N, C::TransitionStorage> {
        self.storage.transition_store()
    }

    /// Starts an atomic batch write operation.
    pub fn start_atomic(&self) {
        self.storage.start_atomic();
    }

    /// Checks if an atomic batch is in progress.
    pub fn is_atomic_in_progress(&self) -> bool {
        self.storage.is_atomic_in_progress()
    }

    /// Aborts an atomic batch write operation.
    pub fn abort_atomic(&self) {
        self.storage.abort_atomic();
    }

    /// Finishes an atomic batch write operation.
    pub fn finish_atomic(&self) -> Result<()> {
        self.storage.finish_atomic()
    }

    /// Returns the optional development ID.
    pub fn dev(&self) -> Option<u16> {
        self.storage.dev()
    }
}
