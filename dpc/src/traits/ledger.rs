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

use crate::{BlockScheme, Network};
use snarkvm_algorithms::merkle_tree::MerklePath;

use anyhow::Result;
use std::path::Path;

pub trait LedgerScheme<N: Network>: Sized {
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
    fn get_block(&self, block_hash: &N::BlockHash) -> Result<Self::Block>;

    /// Returns the block hash given a block number.
    fn get_block_hash(&self, block_number: u32) -> Result<N::BlockHash>;

    /// Returns the block number given a block hash.
    fn get_block_number(&self, block_hash: &N::BlockHash) -> Result<u32>;

    /// Returns true if the given block hash exists in the ledger.
    fn contains_block_hash(&self, block_hash: &N::BlockHash) -> bool;
}

/// The state commitments tree is a core state tree of the ledger.
pub trait CommitmentsTreeScheme<N: Network>: Sized {
    /// Initializes an empty commitments tree.
    fn new() -> Result<Self>;

    /// Adds the given commitment to the tree, returning its index in the tree.
    fn add(&mut self, commitment: &N::Commitment) -> Result<u32>;

    /// Adds all given commitments to the tree, returning the start and ending index in the tree.
    fn add_all(&mut self, commitments: Vec<N::Commitment>) -> Result<(u32, u32)>;

    /// Returns `true` if the given commitment exists.
    fn contains_commitment(&self, commitment: &N::Commitment) -> bool;

    /// Returns the index for the given commitment, if it exists.
    fn get_commitment_index(&self, commitment: &N::Commitment) -> Option<&u32>;

    /// Returns the Merkle path for a given commitment.
    fn to_commitment_inclusion_proof(
        &self,
        commitment: &N::Commitment,
    ) -> Result<MerklePath<N::CommitmentsTreeParameters>>;

    /// Returns the commitments root.
    fn to_commitments_root(&self) -> &N::CommitmentsRoot;
}

/// The ledger serial numbers tree is a core state tree of the ledger.
pub trait SerialNumbersTreeScheme<N: Network>: Sized {
    /// Initializes an empty serial numbers tree.
    fn new() -> Result<Self>;

    /// Adds the given serial number to the tree, returning its index in the tree.
    fn add(&mut self, serial_number: &N::SerialNumber) -> Result<u32>;

    /// Adds all given serial numbers to the tree, returning the start and ending index in the tree.
    fn add_all(&mut self, serial_numbers: Vec<N::SerialNumber>) -> Result<(u32, u32)>;

    /// Returns `true` if the given serial number exists.
    fn contains_serial_number(&self, serial_number: &N::SerialNumber) -> bool;

    /// Returns the index for the given serial number, if it exists.
    fn get_serial_number_index(&self, serial_number: &N::SerialNumber) -> Option<&u32>;

    /// Returns the Merkle path for a given serial number.
    fn to_serial_number_inclusion_proof(
        &self,
        serial_number: &N::SerialNumber,
    ) -> Result<MerklePath<N::SerialNumbersTreeParameters>>;

    /// Returns the serial numbers root.
    fn to_serial_numbers_root(&self) -> &N::SerialNumbersRoot;
}
