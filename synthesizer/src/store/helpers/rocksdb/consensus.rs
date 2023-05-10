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
    helpers::rocksdb::{BlockDB, FinalizeDB, TransactionDB, TransitionDB},
    BlockStore,
    ConsensusStorage,
    FinalizeStore,
};
use console::prelude::*;

/// An RocksDB consensus storage.
#[derive(Clone)]
pub struct ConsensusDB<N: Network> {
    /// The finalize store.
    finalize_store: FinalizeStore<N, FinalizeDB<N>>,
    /// The block store.
    block_store: BlockStore<N, BlockDB<N>>,
}

#[rustfmt::skip]
impl<N: Network> ConsensusStorage<N> for ConsensusDB<N> {
    type FinalizeStorage = FinalizeDB<N>;
    type BlockStorage = BlockDB<N>;
    type TransactionStorage = TransactionDB<N>;
    type TransitionStorage = TransitionDB<N>;

    /// Initializes the consensus storage.
    fn open(dev: Option<u16>) -> Result<Self> {
        // Initialize the finalize store.
        let finalize_store = FinalizeStore::<N, FinalizeDB<N>>::open(dev)?;
        // Initialize the block store.
        let block_store = BlockStore::<N, BlockDB<N>>::open(dev)?;
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
