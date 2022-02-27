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

use crate::Network;
use snarkvm_algorithms::merkle_tree::MerklePath;

use anyhow::Result;

/// The ledger tree is a core state tree.
pub trait LedgerTreeScheme<N: Network>: Sized {
    /// Initializes an empty ledger tree.
    fn new() -> Result<Self>;

    /// Adds the given commitment to the tree, returning its index in the tree.
    fn add(&mut self, block_hash: &N::BlockHash) -> Result<u32>;

    /// Adds all given block hashes to the tree, returning the start and ending index in the tree.
    fn add_all(&mut self, block_hashes: &[N::BlockHash]) -> Result<(u32, u32)>;

    /// Returns `true` if the given block hash exists.
    fn contains_block_hash(&self, block_hash: &N::BlockHash) -> bool;

    /// Returns the index for the given block hash, if it exists.
    fn get_block_hash_index(&self, block_hash: &N::BlockHash) -> Option<&u32>;

    /// Returns the ledger root.
    fn root(&self) -> N::LedgerRoot;

    /// Returns the Merkle path for a given block hash.
    fn to_ledger_inclusion_proof(&self, block_hash: &N::BlockHash) -> Result<MerklePath<N::LedgerRootParameters>>;
}
