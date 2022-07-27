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

// mod blocks;
// pub use blocks::*;

mod state_path;
pub use state_path::*;

mod vm;
pub use vm::*;

use crate::console::{
    collections::merkle_tree::MerklePath,
    network::{prelude::*, BHPMerkleTree},
    types::Field,
};
use snarkvm_compiler::Program;

use indexmap::{IndexMap, IndexSet};

/// The depth of the Merkle tree for the blocks.
const BLOCKS_DEPTH: u8 = 32;

/// The Merkle tree for the blocks.
pub type BlockTree<N> = BHPMerkleTree<N, BLOCKS_DEPTH>;
/// The Merkle path for the blocks.
pub type BlockPath<N> = MerklePath<N, BLOCKS_DEPTH>;

#[derive(Clone)]
#[allow(dead_code)]
pub struct Ledger<N: Network> {
    /// The mapping of block numbers to blocks.
    blocks: IndexMap<u32, Block<N>>,
    /// The mapping of program IDs to their programs.
    programs: IndexMap<u64, Program<N>>,
    // /// The mapping of program IDs to their global state.
    // states: IndexMap<u64, IndexMap<Identifier<N>, Plaintext<N>>>,
    /// The memory pool of unconfirmed transactions.
    memory_pool: IndexSet<Transaction<N>>,
    /// The current state tree.
    state_tree: BlockTree<N>,
}

impl<N: Network> Ledger<N> {
    /// Initializes a new ledger.
    pub fn new() -> Result<Self> {
        // TODO (raychu86): Inject the genesis block.
        Ok(Self {
            programs: IndexMap::new(),
            blocks: IndexMap::new(),
            memory_pool: IndexSet::new(),
            state_tree: N::merkle_tree_bhp(&vec![])?,
        })
    }

    /// Returns an iterator over all transactions in `self` that are deployments.
    pub fn deployments(&self) -> impl '_ + Iterator<Item = &Transaction<N>> {
        self.blocks.values().flat_map(|block| block.deployments())
    }

    /// Returns an iterator over all transactions in `self` that are executions.
    pub fn executions(&self) -> impl '_ + Iterator<Item = &Transaction<N>> {
        self.blocks.values().flat_map(|block| block.executions())
    }

    /// Returns the latest state root of the ledger.
    pub fn latest_state_root(&self) -> &Field<N> {
        &self.state_tree.root()
    }

    /// Returns the height of the latest block.
    pub fn latest_block_height(&self) -> u32 {
        *self.blocks.keys().max().unwrap_or(&0u32)
    }

    /// Returns the hash of the latest block.
    pub fn latest_block_hash(&self) -> N::BlockHash {
        self.blocks.get(&self.latest_block_height()).map(|block| block.hash()).unwrap_or(N::BlockHash::default())
    }

    /// Returns the previous block hash given the block height.
    pub fn get_previous_block_hash(&self, height: u32) -> Result<N::BlockHash> {
        match self.blocks.get(&height) {
            Some(block) => Ok(block.previous_hash()),
            None => Err(anyhow!("Missing previous block hash for height {}", height)),
        }
    }

    /// Returns the block at a givenblock height.
    pub fn get_block(&self, height: u32) -> Result<&Block<N>> {
        match self.blocks.get(&height) {
            Some(block) => Ok(block),
            None => Err(anyhow!("Missing block for height {}", height)),
        }
    }

    /// Returns `true` if the given block height exists on the canon chain.
    pub fn contains_block_height(&self, height: u32) -> bool {
        self.blocks.contains_key(&height)
    }

    /// Returns `true` if the given block hash exists on the canon chain.
    pub fn contains_block_hash(&self, hash: &N::BlockHash) -> bool {
        self.blocks.values().any(|block| &block.hash() == hash)
    }

    /// Adds the given canon block, if it is well-formed and does not already exist.
    pub fn add_next_block(&mut self, vm: &VM<N>, block: &Block<N>) -> Result<()> {
        // TODO (raychu86): Handle block verification.
        // Ensure the block itself is valid.
        if !block.verify(vm) {
            return Err(anyhow!("The given block is invalid"));
        }

        // Ensure the next block height is correct.
        let height = block.header().height();
        if self.latest_block_height() + 1 != height {
            return Err(anyhow!("The given block has an incorrect block height"));
        }

        // Ensure the block height does not already exist.
        if self.contains_block_height(height) {
            return Err(anyhow!("The given block height already exists in the ledger"));
        }

        // Ensure the previous block hash is correct.
        if self.latest_block_hash() != block.previous_hash() {
            return Err(anyhow!("The given block has an incorrect previous block hash"));
        }

        // Ensure the block hash does not already exist.
        let block_hash = block.hash();
        if self.contains_block_hash(&block_hash) {
            return Err(anyhow!("The given block hash already exists in the ledger"));
        }

        // TODO (raychu86): Add timestamp and difficulty verification.

        // TODO (raychu86): Handle state path verification.

        // TODO (raychu86): Update the state_tree.
        self.state_tree.append(&[block.hash().to_bits_le()])?;

        Ok(())
    }

    /// Returns the state path for a given commitment.
    pub fn to_state_path(&self, commitment: &Field<N>) -> Result<StatePath<N>> {
        // TODO (raychu86): Add support for input and output ids.
        // Find the transaction that contains the record commitment.
        let transaction = self
            .blocks
            .iter()
            .flat_map(|(_, block)| &**block.transactions())
            .filter(|(_, transaction)| transaction.commitments().contains(&commitment))
            .collect::<Vec<_>>();

        if transaction.len() != 1 {
            return Err(anyhow!("Multiple transactions associated with commitment {}", commitment.to_string()));
        }

        let (transaction_id, transaction) = transaction[0];

        // Find the block that contains the record commitment.
        let block = self
            .blocks
            .iter()
            .filter(|(_, block)| block.transactions().transaction_ids().contains(&transaction_id))
            .collect::<Vec<_>>();

        if block.len() != 1 {
            return Err(anyhow!("Multiple blocks associated with transaction id {}", transaction_id.to_string()));
        }

        let (_, block) = block[0];
        let block_header = block.header();

        // Find the transition that contains the record commitment.
        let transition = transaction
            .transitions()
            .filter(|transition| transition.commitments().contains(&commitment))
            .collect::<Vec<_>>();

        if transition.len() != 1 {
            return Err(anyhow!("Multiple transitions associated with commitment {}", commitment.to_string()));
        }

        let transition = transition[0];
        let transition_id = transition.id();

        // Construct the transition path and transaction leaf.
        let transition_leaf = transition.to_leaf(commitment, false)?;
        let transition_path = transition.to_path(&transition_leaf)?;

        // Construct the transaction path and transaction leaf.
        let transaction_leaf = transaction.to_leaf(transition_id)?;
        let transaction_path = transaction.to_path(&transaction_leaf)?;

        // Construct the transactions path.
        let transactions = block.transactions();
        let transaction_index = transactions.iter().position(|(id, _)| id == transaction_id).unwrap();
        let transactions_path = transactions.to_path(transaction_index, **transaction_id)?;

        // Construct the block header path.
        let header_root = block_header.to_root()?;
        let header_leaf = HeaderLeaf::<N>::new(1, transaction.to_root()?);
        let header_path = block_header.to_path(&header_leaf)?;

        // Construct the block path.
        let latest_block_height = self.latest_block_height();
        let latest_block_hash = self.latest_block_hash();
        let previous_block_hash = self.get_previous_block_hash(latest_block_height)?;

        let state_root = self.latest_state_root().clone();
        let block_path = self.state_tree.prove(latest_block_height as usize, &latest_block_hash.to_bits_le())?;

        StatePath::new(
            state_root.into(),
            block_path,
            latest_block_hash,
            previous_block_hash,
            header_root,
            header_path,
            header_leaf,
            transactions_path,
            *transaction_id,
            transaction_path,
            transaction_leaf,
            transition_path,
            transition_leaf,
        )
    }
}

impl<N: Network> Default for Ledger<N> {
    fn default() -> Self {
        Self {
            programs: IndexMap::new(),
            blocks: IndexMap::new(),
            memory_pool: IndexSet::new(),
            state_tree: N::merkle_tree_bhp(&vec![]).unwrap(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_deploy() -> Result<()> {
        // Initialize a new ledger.
        let _ledger = Ledger::<CurrentNetwork>::new().unwrap();

        Ok(())
    }
}
