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

use crate::prelude::*;
use snarkvm_algorithms::{
    merkle_tree::{MerklePath, MerkleTree},
    prelude::*,
};
use snarkvm_utilities::has_duplicates;

use anyhow::{anyhow, Result};
use std::{collections::HashMap, sync::Arc};

/// A ledger tree contains all block hashes on the ledger.
#[derive(Clone, Derivative)]
#[derivative(Debug(bound = "N: Network"))]
pub struct LedgerTree<N: Network> {
    #[derivative(Debug = "ignore")]
    tree: Arc<MerkleTree<N::LedgerRootParameters>>,
    block_hashes: HashMap<N::BlockHash, u32>,
    current_index: u32,
}

impl<N: Network> LedgerTreeScheme<N> for LedgerTree<N> {
    /// Initializes an empty ledger tree.
    fn new() -> Result<Self> {
        Ok(Self {
            tree: Arc::new(MerkleTree::<N::LedgerRootParameters>::new::<N::BlockHash>(
                Arc::new(N::ledger_root_parameters().clone()),
                &[],
            )?),
            block_hashes: Default::default(),
            current_index: 0,
        })
    }

    /// Adds the given block hash to the tree, returning its index in the tree.
    fn add(&mut self, block_hash: &N::BlockHash) -> Result<u32> {
        // Ensure the block_hash does not already exist in the tree.
        if self.contains_block_hash(block_hash) {
            return Err(MerkleError::Message(format!("{} already exists in the ledger tree", block_hash)).into());
        }

        self.tree = Arc::new(self.tree.rebuild(self.current_index as usize, &[block_hash])?);
        self.block_hashes.insert(*block_hash, self.current_index);

        let current_index = self.current_index;
        self.current_index = current_index
            .checked_add(1)
            .ok_or_else(|| anyhow!("The index exceeds the maximum number of allowed block hashes."))?;

        Ok(current_index)
    }

    /// Adds all given block hashes to the tree, returning the start and ending index in the tree.
    fn add_all(&mut self, block_hashes: &[N::BlockHash]) -> Result<(u32, u32)> {
        // Ensure the list of given block hashes is non-empty.
        if block_hashes.is_empty() {
            return Err(anyhow!("The list of given block hashes must be non-empty"));
        }

        // Ensure the list of given block hashes is unique.
        if has_duplicates(block_hashes.iter()) {
            return Err(anyhow!("The list of given block hashes contains duplicates"));
        }

        // Ensure the block hashes do not already exist in the tree.
        if block_hashes.iter().any(|c| self.contains_block_hash(c)) {
            return Err(anyhow!("The list of given block hashes contains duplicates"));
        }

        let start_index = self.current_index;
        let num_block_hashes = block_hashes.len();

        // Ensure that the number of block hashes does not exceed the u32 bounds of `self.current_index`.
        if (self.current_index as usize).saturating_add(num_block_hashes) > u32::MAX as usize {
            return Err(anyhow!("The ledger tree will reach its maximum size."));
        }

        // Add the block hashes to the tree. Start the tree from scratch if the tree is currently empty.
        self.tree = match self.current_index {
            0 => Arc::new(MerkleTree::<N::LedgerRootParameters>::new::<N::BlockHash>(
                Arc::new(N::ledger_root_parameters().clone()),
                block_hashes,
            )?),
            _ => Arc::new(self.tree.rebuild(self.current_index as usize, block_hashes)?),
        };

        self.block_hashes.extend(
            block_hashes.iter().enumerate().map(|(index, block_hash)| (*block_hash, start_index + index as u32)),
        );

        self.current_index = self
            .current_index
            .checked_add(num_block_hashes as u32)
            .ok_or_else(|| anyhow!("The index exceeds the maximum number of allowed block hashes."))?;
        let end_index = self.current_index.checked_sub(1).ok_or_else(|| anyhow!("Integer underflow."))?;

        Ok((start_index, end_index))
    }

    /// Returns `true` if the given block hash exists.
    fn contains_block_hash(&self, block_hash: &N::BlockHash) -> bool {
        self.block_hashes.contains_key(block_hash)
    }

    /// Returns the index for the given block hash, if it exists.
    fn get_block_hash_index(&self, block_hash: &N::BlockHash) -> Option<&u32> {
        self.block_hashes.get(block_hash)
    }

    /// Returns the ledger root.
    fn root(&self) -> N::LedgerRoot {
        (*self.tree.root()).into()
    }

    /// Returns the Merkle path for a given block hash.
    fn to_ledger_inclusion_proof(&self, block_hash: &N::BlockHash) -> Result<MerklePath<N::LedgerRootParameters>> {
        match self.get_block_hash_index(block_hash) {
            Some(index) => Ok(self.tree.generate_proof(*index as usize, block_hash)?),
            _ => Err(MerkleError::MissingLeaf(format!("{}", block_hash)).into()),
        }
    }
}

impl<N: Network> Default for LedgerTree<N> {
    fn default() -> Self {
        Self::new().unwrap()
    }
}
