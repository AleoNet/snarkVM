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
};
use snarkvm_compiler::Program;

use indexmap::{IndexMap, IndexSet};

/// The depth of the Merkle tree for the blocks.
const BLOCKS_DEPTH: u8 = 32;

/// The Merkle tree for the blocks.
pub type BlockTree<N> = BHPMerkleTree<N, BLOCKS_DEPTH>;
/// The Merkle path for the blocks.
pub type BlockPath<N> = MerklePath<N, BLOCKS_DEPTH>;

#[derive(Clone, Default)]
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
}

impl<N: Network> Ledger<N> {
    /// Initializes a new ledger.
    pub fn new() -> Self {
        Self { programs: IndexMap::new(), blocks: IndexMap::new(), memory_pool: IndexSet::new() }
    }

    /// Returns an iterator over all transactions in `self` that are deployments.
    pub fn deployments(&self) -> impl '_ + Iterator<Item = &Transaction<N>> {
        self.blocks.values().flat_map(|block| block.deployments())
    }

    /// Returns an iterator over all transactions in `self` that are executions.
    pub fn executions(&self) -> impl '_ + Iterator<Item = &Transaction<N>> {
        self.blocks.values().flat_map(|block| block.executions())
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
        let _ledger = Ledger::<CurrentNetwork>::new();

        Ok(())
    }
}
