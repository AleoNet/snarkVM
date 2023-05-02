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

use crate::store::{
    helpers::memory::{BlockMemory, FinalizeMemory, TransactionMemory, TransitionMemory},
    BlockStore,
    ConsensusStorage,
    FinalizeStore,
};
use console::prelude::*;

/// An in-memory consensus storage.
#[derive(Clone)]
pub struct ConsensusMemory<N: Network> {
    /// The finalize store.
    finalize_store: FinalizeStore<N, FinalizeMemory<N>>,
    /// The block store.
    block_store: BlockStore<N, BlockMemory<N>>,
}

#[rustfmt::skip]
impl<N: Network> ConsensusStorage<N> for ConsensusMemory<N> {
    type FinalizeStorage = FinalizeMemory<N>;
    type BlockStorage = BlockMemory<N>;
    type TransactionStorage = TransactionMemory<N>;
    type TransitionStorage = TransitionMemory<N>;

    /// Initializes the consensus storage.
    fn open(dev: Option<u16>) -> Result<Self> {
        // Initialize the finalize store.
        let finalize_store = FinalizeStore::<N, FinalizeMemory<N>>::open(dev)?;
        // Initialize the block store.
        let block_store = BlockStore::<N, BlockMemory<N>>::open(dev)?;
        // Return the consensus storage.
        Ok(Self {
            finalize_store,
            block_store,
        })
    }

    /// Returns the finalize store.
    fn finalize_store(&self) -> &FinalizeStore<N, Self::FinalizeStorage> {
        &self.finalize_store
    }

    /// Returns the block store.
    fn block_store(&self) -> &BlockStore<N, Self::BlockStorage> {
        &self.block_store
    }
}
