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

mod block;
pub use block::*;

mod blocks;
pub use blocks::*;

mod state_path;
pub use state_path::*;

mod vm;
pub use vm::*;

mod map;
pub use map::*;

use crate::console::{network::prelude::*, types::Field};
use snarkvm_compiler::Program;

use indexmap::{IndexMap, IndexSet};

#[derive(Clone)]
#[allow(dead_code)]
pub struct Ledger<N: Network> {
    /// The mapping of block numbers to blocks.
    blocks: Blocks<N>,
    /// The mapping of program IDs to their programs.
    programs: IndexMap<u64, Program<N>>,
    // /// The mapping of program IDs to their global state.
    // states: IndexMap<u64, IndexMap<Identifier<N>, Plaintext<N>>>,
    /// The memory pool of unconfirmed transactions.
    memory_pool: IndexSet<Transaction<N>>,
}

impl<N: Network> Ledger<N> {
    /// Initializes a new ledger.
    pub fn new() -> Result<Self> {
        Ok(Self { programs: IndexMap::new(), blocks: Blocks::new()?, memory_pool: IndexSet::new() })
    }

    /// Returns an iterator over all transactions in `self` that are deployments.
    pub fn deployments(&self) -> impl '_ + Iterator<Item = &Transaction<N>> {
        self.blocks.transactions.values().flat_map(|transactions| transactions.deployments())
    }

    /// Returns an iterator over all transactions in `self` that are executions.
    pub fn executions(&self) -> impl '_ + Iterator<Item = &Transaction<N>> {
        self.blocks.transactions.values().flat_map(|transactions| transactions.executions())
    }

    /// Returns the latest state root of the ledger.
    pub fn latest_state_root(&self) -> &Field<N> {
        self.blocks.latest_state_root()
    }

    /// Returns the height of the latest block.
    pub fn latest_block_height(&self) -> u32 {
        self.blocks.latest_height()
    }

    /// Returns the height of the latest block.
    pub fn latest_block(&self) -> Result<Block<N>> {
        self.blocks.latest_block()
    }

    /// Returns the hash of the latest block.
    pub fn latest_block_hash(&self) -> N::BlockHash {
        self.blocks.latest_hash()
    }

    /// Returns the previous block hash given the block height.
    pub fn get_previous_block_hash(&self, height: u32) -> Result<N::BlockHash> {
        self.blocks.get_previous_hash(height)
    }

    /// Returns the block at a given block height.
    pub fn get_block(&self, height: u32) -> Result<Block<N>> {
        self.blocks.get_block(height)
    }

    /// Returns `true` if the given block height exists on the canon chain.
    pub fn contains_block_height(&self, height: u32) -> Result<bool> {
        self.blocks.contains_height(height)
    }

    /// Returns `true` if the given block hash exists on the canon chain.
    pub fn contains_block_hash(&self, hash: &N::BlockHash) -> bool {
        self.blocks.contains_block_hash(hash)
    }

    /// Returns a proposal block constructed with the transactions in the mempool.
    pub fn propose_block(&self, transactions: Transactions<N>) -> Result<Block<N>> {
        self.blocks.propose_block(transactions)
    }

    /// Adds the given canon block, if it is well-formed and does not already exist.
    pub fn add_next_block(&mut self, _vm: &VM<N>, block: &Block<N>) -> Result<()> {
        self.blocks.add_next(block)?;

        // TODO (raychu86): Add deployed programs to the ledger.

        Ok(())
    }

    /// Returns the state path for a given commitment.
    pub fn to_state_path(&self, commitment: &Field<N>) -> Result<StatePath<N>> {
        self.blocks.to_state_path(commitment)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{console::network::Testnet3, test_helpers::sample_execution_transaction};

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_deploy() {
        // Initialize a new ledger.
        let _ledger = Ledger::<CurrentNetwork>::new().unwrap();
    }

    #[test]
    fn test_new_blocks() {
        // Initialize a new ledger.
        let mut ledger = Ledger::<CurrentNetwork>::new().unwrap();

        // Retrieve the genesis block.
        let genesis = ledger.get_block(0).unwrap();

        assert_eq!(ledger.latest_block_height(), 0);
        assert_eq!(ledger.latest_block_hash(), genesis.hash());

        // Construct a new block.
        let new_transaction = sample_execution_transaction();
        let transactions = Transactions::from(&[new_transaction]).unwrap();

        // Initialize the VM.
        // TODO (raychu86): This VM needs to have the program deployments to verify blocks properly.
        let vm = VM::<CurrentNetwork>::new().unwrap();

        let new_block = ledger.propose_block(transactions).unwrap();
        ledger.add_next_block(&vm, &new_block).unwrap();

        assert_eq!(ledger.latest_block_height(), 1);
        assert_eq!(ledger.latest_block_hash(), new_block.hash());
    }
}
