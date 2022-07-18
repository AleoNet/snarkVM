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

mod header;
pub use header::*;

mod transaction;
pub use transaction::*;

mod transactions;
pub use transactions::*;

mod bytes;
mod genesis;
mod serialize;
mod string;

use crate::{
    console::{
        account::{Address, PrivateKey},
        network::prelude::*,
        program::Value,
    },
    ledger::vm::VM,
};
use snarkvm_compiler::Program;

#[derive(Clone, PartialEq, Eq)]
pub struct Block<N: Network> {
    /// The hash of this block.
    block_hash: N::BlockHash,
    /// The hash of the previous block.
    previous_hash: N::BlockHash,
    /// The header of the block.
    header: Header<N>,
    /// The transactions in the block.
    transactions: Transactions<N>,
}

impl<N: Network> Block<N> {
    /// Initializes a new block from a given previous hash, header, and transactions list.
    pub fn from(previous_hash: N::BlockHash, header: Header<N>, transactions: Transactions<N>) -> Result<Self> {
        // Ensure the block is not empty.
        ensure!(!transactions.is_empty(), "Cannot create block with no transactions");
        // Compute the block hash.
        let block_hash =
            N::hash_bhp1024(&[previous_hash.to_bits_le(), header.to_root()?.to_bits_le()].concat())?.into();
        // Construct the block.
        Ok(Self { block_hash, previous_hash, header, transactions })
    }

    /// Returns `true` if the block is well-formed.
    pub fn verify(&self, vm: &VM<N>) -> bool {
        // If the block is the genesis block, check that it is valid.
        if self.header.height() == 0 && !self.is_genesis() {
            warn!("Invalid genesis block");
            return false;
        }

        // Ensure the block header is valid.
        if !self.header.is_valid() {
            warn!("Invalid block header: {:?}", self.header);
            return false;
        }

        // Compute the Merkle root of the block header.
        let header_root = match self.header.to_root() {
            Ok(root) => root,
            Err(error) => {
                warn!("Failed to compute the Merkle root of the block header: {error}");
                return false;
            }
        };

        // Check the block hash.
        match N::hash_bhp1024(&[self.previous_hash.to_bits_le(), header_root.to_bits_le()].concat()) {
            Ok(candidate_hash) => {
                // Ensure the block hash matches the one in the block.
                if candidate_hash != *self.block_hash {
                    warn!("Block ({}) has an incorrect block hash.", self.block_hash);
                    return false;
                }
            }
            Err(error) => {
                warn!("Unable to compute block hash for block ({}): {error}", self.block_hash);
                return false;
            }
        };

        // Compute the transactions root.
        match self.transactions.to_root() {
            // Ensure the transactions root matches the one in the block header.
            Ok(root) => {
                if &root != self.header.transactions_root() {
                    warn!(
                        "Block ({}) has an incorrect transactions root: expected {}",
                        self.block_hash,
                        self.header.transactions_root()
                    );
                    return false;
                }
            }
            Err(error) => {
                warn!("Failed to compute the Merkle root of the block transactions: {error}");
                return false;
            }
        };

        // Ensure the transactions are valid.
        if !self.transactions.verify(vm) {
            warn!("Block contains invalid transactions: {:?}", self);
            return false;
        }

        true
    }

    /// Returns the block hash.
    pub const fn hash(&self) -> N::BlockHash {
        self.block_hash
    }

    /// Returns the previous block hash.
    pub const fn previous_hash(&self) -> N::BlockHash {
        self.previous_hash
    }

    /// Returns the block header.
    pub const fn header(&self) -> &Header<N> {
        &self.header
    }

    /// Returns the transactions in the block.
    pub const fn transactions(&self) -> &Transactions<N> {
        &self.transactions
    }
}

impl<N: Network> Block<N> {
    /// Returns an iterator over all transactions in `self` that are deployments.
    pub fn deployments(&self) -> impl '_ + Iterator<Item = &Transaction<N>> {
        self.transactions.deployments()
    }

    /// Returns an iterator over all transactions in `self` that are executions.
    pub fn executions(&self) -> impl '_ + Iterator<Item = &Transaction<N>> {
        self.transactions.executions()
    }
}
