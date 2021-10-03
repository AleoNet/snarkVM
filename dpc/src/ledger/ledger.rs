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

use crate::prelude::*;

use anyhow::{anyhow, Result};
use std::collections::HashSet;

#[derive(Clone, Debug)]
pub struct Ledger<N: Network> {
    /// The canonical chain of blocks.
    canon_blocks: Blocks<N>,
    /// The set of unknown orphan blocks.
    orphan_blocks: HashSet<Block<N>>,
    /// The pool of unconfirmed transactions.
    memory_pool: MemoryPool<N>,
    /// The operating mode of this ledger.
    is_full_node: bool,
}

impl<N: Network> Ledger<N> {
    /// Initializes a new instance of the ledger.
    pub fn new(is_full_node: bool) -> Result<Self> {
        Ok(Self {
            canon_blocks: Blocks::new()?,
            orphan_blocks: Default::default(),
            memory_pool: MemoryPool::new(),
            is_full_node,
        })
    }

    /// Adds the given canon block, if it is well-formed and does not already exist.
    /// Note: This method requires blocks to be added in order of canon block height.
    pub fn add_next_block(&mut self, block: &Block<N>) -> Result<()> {
        // Noop if this node is not a full node.
        if !self.is_full_node {
            return Ok(());
        }

        // Attempt to insert the block into canon.
        self.canon_blocks.add_next(block)?;

        Ok(())
    }

    /// Adds the given orphan block, if it is well-formed and does not already exist.
    pub fn add_orphan_block(&mut self, block: &Block<N>) -> Result<()> {
        // Noop if this node is not a full node.
        if !self.is_full_node {
            return Ok(());
        }

        // Ensure the block does not exist in canon.
        if self.canon_blocks.contains_block_hash(&block.to_block_hash()?) {
            return Err(anyhow!("Orphan block already exists in canon chain"));
        }

        // Insert the block into the orphan blocks.
        self.orphan_blocks.insert(block.clone());

        Ok(())
    }

    /// Adds the given unconfirmed transaction to the memory pool.
    pub fn add_unconfirmed_transaction(&mut self, transaction: &Transaction<N>) -> Result<()> {
        // Noop if this node is not a full node.
        if !self.is_full_node {
            return Ok(());
        }

        // Attempt to add the transaction into the memory pool.
        self.memory_pool.add(transaction)?;

        Ok(())
    }

    // pub fn mine(&mut self) -> Result<()> {
    //     // Noop if this node is not a full node.
    //     if !self.is_full_node {
    //         return Ok(());
    //     }
    // }
}
