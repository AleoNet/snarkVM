// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::{BlockHash, BlockScheme};
use snarkvm_dpc::{LedgerCommitmentsTree, LedgerSerialNumbersTree, Network};

use anyhow::Result;
use std::path::Path;

pub trait LedgerScheme<C: Network>: LedgerCommitmentsTree<C> + LedgerSerialNumbersTree<C> + Sized {
    type Block: BlockScheme;

    /// Instantiates a new ledger with a genesis block.
    fn new(path: Option<&Path>, genesis_block: Self::Block) -> Result<Self>;

    /// Returns the latest number of blocks in the ledger.
    /// A block height of 0 indicates the ledger is uninitialized.
    /// A block height of 1 indicates the ledger is initialized with a genesis block.
    fn block_height(&self) -> u32;

    /// Returns the latest block in the ledger.
    fn latest_block(&self) -> Result<Self::Block>;

    /// Returns the block given the block hash.
    fn get_block(&self, block_hash: &BlockHash) -> Result<Self::Block>;

    /// Returns the block hash given a block number.
    fn get_block_hash(&self, block_number: u32) -> Result<BlockHash>;

    /// Returns the block number given a block hash.
    fn get_block_number(&self, block_hash: &BlockHash) -> Result<u32>;

    /// Returns true if the given block hash exists in the ledger.
    fn contains_block_hash(&self, block_hash: &BlockHash) -> bool;
}
