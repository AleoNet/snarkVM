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

pub mod circuit;

mod bytes;
mod parse;
mod serialize;

use crate::{
    block::{
        BlockPath,
        HeaderLeaf,
        HeaderPath,
        TransactionLeaf,
        TransactionPath,
        TransactionsPath,
        TransitionLeaf,
        TransitionPath,
    },
    BlockStorage,
    BlockStore,
    BlockTree,
};
use console::{network::prelude::*, types::Field};

#[derive(Clone, PartialEq, Eq)]
pub struct StatePath<N: Network> {
    /// The state root.
    state_root: N::StateRoot,
    /// The Merkle path for the block hash.
    block_path: BlockPath<N>,
    /// The block hash.
    block_hash: N::BlockHash,
    /// The previous block hash.
    previous_block_hash: N::BlockHash,
    /// The block header root.
    header_root: Field<N>,
    /// The Merkle path for the block header leaf.
    header_path: HeaderPath<N>,
    /// The block header leaf.
    header_leaf: HeaderLeaf<N>,
    /// The Merkle path for the transaction ID.
    transactions_path: TransactionsPath<N>,
    /// The transaction ID.
    transaction_id: N::TransactionID,
    /// The Merkle path for the transaction leaf.
    transaction_path: TransactionPath<N>,
    /// The transaction leaf.
    transaction_leaf: TransactionLeaf<N>,
    /// The Merkle path for the transition leaf.
    transition_path: TransitionPath<N>,
    /// The transition leaf.
    transition_leaf: TransitionLeaf<N>,
}

impl<N: Network> StatePath<N> {
    /// Returns a state path for the given commitment.
    pub fn new_commitment<B: BlockStorage<N>>(
        block_tree: &BlockTree<N>,
        blocks: &BlockStore<N, B>,
        commitment: &Field<N>,
    ) -> Result<StatePath<N>> {
        // Retrieve the transaction and transition store.
        let transactions = blocks.transaction_store();
        let transitions = blocks.transition_store();

        // Ensure the commitment exists.
        if !transitions.contains_commitment(commitment)? {
            bail!("Commitment '{commitment}' does not exist");
        }

        // Find the transition that contains the commitment.
        let transition_id = transitions.find_transition_id(commitment)?;
        // Find the transaction that contains the transition.
        let transaction_id = match transactions.find_transaction_id(&transition_id)? {
            Some(transaction_id) => transaction_id,
            None => bail!("The transaction ID for commitment '{commitment}' is not in the ledger"),
        };
        // Find the block that contains the transaction.
        let block_hash = match blocks.find_block_hash(&transaction_id)? {
            Some(block_hash) => block_hash,
            None => bail!("The block hash for commitment '{commitment}' is not in the ledger"),
        };

        // Retrieve the transition.
        let transition = match transitions.get_transition(&transition_id)? {
            Some(transition) => transition,
            None => bail!("The transition '{transition_id}' for commitment '{commitment}' is not in the ledger"),
        };
        // Retrieve the transaction.
        let transaction = match transactions.get_transaction(&transaction_id)? {
            Some(transaction) => transaction,
            None => bail!("The transaction '{transaction_id}' for commitment '{commitment}' is not in the ledger"),
        };
        // Retrieve the block.
        let block = match blocks.get_block(&block_hash)? {
            Some(block) => block,
            None => bail!("The block '{block_hash}' for commitment '{commitment}' is not in the ledger"),
        };

        // Construct the transition path and transaction leaf.
        let transition_leaf = transition.to_leaf(commitment, false)?;
        let transition_path = transition.to_path(&transition_leaf)?;

        // Construct the transaction path and transaction leaf.
        let transaction_leaf = transaction.to_leaf(transition.id())?;
        let transaction_path = transaction.to_path(&transaction_leaf)?;

        // Construct the transactions path.
        let transactions = block.transactions();
        let transaction_index = transactions.iter().position(|(id, _)| id == &transaction.id()).unwrap();
        let transactions_path = transactions.to_path(transaction_index, *transaction.id())?;

        // Construct the block header path.
        let block_header = block.header();
        let header_root = block_header.to_root()?;
        let header_leaf = HeaderLeaf::<N>::new(1, block_header.transactions_root());
        let header_path = block_header.to_path(&header_leaf)?;

        // Construct the state root and block path.
        let state_root = *block_tree.root();
        let block_path = block_tree.prove(block.height() as usize, &block.hash().to_bits_le())?;

        Self::from(
            state_root.into(),
            block_path,
            block.hash(),
            block.previous_hash(),
            header_root,
            header_path,
            header_leaf,
            transactions_path,
            transaction.id(),
            transaction_path,
            transaction_leaf,
            transition_path,
            transition_leaf,
        )
    }

    /// Initializes a new instance of `StatePath`.
    #[allow(clippy::too_many_arguments)]
    pub fn from(
        state_root: N::StateRoot,
        block_path: BlockPath<N>,
        block_hash: N::BlockHash,
        previous_block_hash: N::BlockHash,
        header_root: Field<N>,
        header_path: HeaderPath<N>,
        header_leaf: HeaderLeaf<N>,
        transactions_path: TransactionsPath<N>,
        transaction_id: N::TransactionID,
        transaction_path: TransactionPath<N>,
        transaction_leaf: TransactionLeaf<N>,
        transition_path: TransitionPath<N>,
        transition_leaf: TransitionLeaf<N>,
    ) -> Result<Self> {
        // Ensure the transition path is valid.
        ensure!(
            N::verify_merkle_path_bhp(&transition_path, &transaction_leaf.id(), &transition_leaf.to_bits_le()),
            "'{}' (an input or output ID) does not belong to '{}' (a function or transition)",
            transition_leaf.id(),
            transaction_leaf.id()
        );
        // Ensure the transaction path is valid.
        ensure!(
            N::verify_merkle_path_bhp(&transaction_path, &transaction_id, &transaction_leaf.to_bits_le()),
            "'{}' (a function or transition) does not belong to transaction '{transaction_id}'",
            transaction_leaf.id(),
        );
        // Ensure the transactions path is valid.
        ensure!(
            N::verify_merkle_path_bhp(&transactions_path, &header_leaf.id(), &transaction_id.to_bits_le()),
            "Transaction '{transaction_id}' does not belong to '{header_leaf}' (a header leaf)",
        );
        // Ensure the header path is valid.
        ensure!(
            N::verify_merkle_path_bhp(&header_path, &header_root, &header_leaf.to_bits_le()),
            "'{header_leaf}' (a header leaf) does not belong to '{block_hash}' (a block header)",
        );
        // Ensure the block hash is correct.
        let preimage = (*previous_block_hash).to_bits_le().into_iter().chain(header_root.to_bits_le().into_iter());
        ensure!(
            *block_hash == N::hash_bhp1024(&preimage.collect::<Vec<_>>())?,
            "Block hash '{block_hash}' is incorrect. Double-check the previous block hash and block header root."
        );
        // Ensure the state root is correct.
        ensure!(
            N::verify_merkle_path_bhp(&block_path, &state_root, &block_hash.to_bits_le()),
            "'{block_hash}' (a block hash) does not belong to '{state_root}' (a state root)",
        );
        // Return the state path.
        Ok(Self {
            state_root,
            block_path,
            block_hash,
            previous_block_hash,
            header_root,
            header_path,
            header_leaf,
            transactions_path,
            transaction_id,
            transaction_path,
            transaction_leaf,
            transition_path,
            transition_leaf,
        })
    }

    /// Returns the state root.
    pub const fn state_root(&self) -> N::StateRoot {
        self.state_root
    }

    /// Returns the block path.
    pub const fn block_path(&self) -> &BlockPath<N> {
        &self.block_path
    }

    /// Returns the block hash.
    pub const fn block_hash(&self) -> N::BlockHash {
        self.block_hash
    }

    /// Returns the previous block hash.
    pub const fn previous_block_hash(&self) -> N::BlockHash {
        self.previous_block_hash
    }

    /// Returns the block header root.
    pub const fn header_root(&self) -> &Field<N> {
        &self.header_root
    }

    /// Returns the header path.
    pub const fn header_path(&self) -> &HeaderPath<N> {
        &self.header_path
    }

    /// Returns the header leaf.
    pub const fn header_leaf(&self) -> &HeaderLeaf<N> {
        &self.header_leaf
    }

    /// Returns the transactions path.
    pub const fn transactions_path(&self) -> &TransactionsPath<N> {
        &self.transactions_path
    }

    /// Returns the transaction ID.
    pub const fn transaction_id(&self) -> &N::TransactionID {
        &self.transaction_id
    }

    /// Returns the Merkle path for the transaction leaf.
    pub const fn transaction_path(&self) -> &TransactionPath<N> {
        &self.transaction_path
    }

    /// Returns the transaction leaf.
    pub const fn transaction_leaf(&self) -> &TransactionLeaf<N> {
        &self.transaction_leaf
    }

    /// Returns the Merkle path for the transition leaf.
    pub const fn transition_path(&self) -> &TransitionPath<N> {
        &self.transition_path
    }

    /// Returns the transition leaf.
    pub const fn transition_leaf(&self) -> &TransitionLeaf<N> {
        &self.transition_leaf
    }
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;
    use crate::{
        block::{Block, BlockTree},
        store::{ConsensusMemory, ConsensusStore},
        vm::VM,
    };
    use console::{network::Testnet3, prelude::Network};
    use snarkvm_utilities::rand::TestRng;

    type CurrentNetwork = Testnet3;

    #[derive(Clone)]
    pub struct TestLedger<N: Network> {
        /// The VM state.
        vm: VM<N, ConsensusMemory<N>>,
        /// The current block tree.
        block_tree: BlockTree<N>,
    }

    impl TestLedger<CurrentNetwork> {
        /// Initializes a new instance of the ledger.
        pub fn new(rng: &mut TestRng) -> Result<Self> {
            // Initialize the genesis block.
            let genesis = crate::vm::test_helpers::sample_genesis_block(rng);

            // Initialize the consensus store.
            let store = ConsensusStore::<CurrentNetwork, ConsensusMemory<CurrentNetwork>>::open(None)?;
            // Initialize a new VM.
            let vm = VM::from(store)?;

            // Initialize the ledger.
            let mut ledger = Self { vm, block_tree: CurrentNetwork::merkle_tree_bhp(&[])? };

            // Add the genesis block.
            ledger.add_next_block(&genesis)?;

            // Return the ledger.
            Ok(ledger)
        }
    }

    impl<N: Network> TestLedger<N> {
        /// Adds the given block as the next block in the chain.
        pub fn add_next_block(&mut self, block: &Block<N>) -> Result<()> {
            /* ATOMIC CODE SECTION */

            // Add the block to the ledger. This code section executes atomically.
            {
                let mut ledger = self.clone();

                // Update the blocks.
                ledger.block_tree.append(&[block.hash().to_bits_le()])?;
                ledger.vm.block_store().insert(*ledger.block_tree.root(), block)?;

                // Update the VM.
                for transaction in block.transactions().values() {
                    ledger.vm.finalize(transaction)?;
                }

                *self = Self { vm: ledger.vm, block_tree: ledger.block_tree };
            }

            Ok(())
        }

        /// Returns the block for the given block height.
        pub fn get_block(&self, height: u32) -> Result<Block<N>> {
            // Retrieve the block hash.
            let block_hash = match self.vm.block_store().get_block_hash(height)? {
                Some(block_hash) => block_hash,
                None => bail!("Block {height} does not exist in storage"),
            };
            // Retrieve the block.
            match self.vm.block_store().get_block(&block_hash)? {
                Some(block) => Ok(block),
                None => bail!("Block {height} ('{block_hash}') does not exist in storage"),
            }
        }

        /// Returns a state path for the given commitment.
        pub fn to_state_path(&self, commitment: &Field<N>) -> Result<StatePath<N>> {
            StatePath::new_commitment(&self.block_tree, self.vm.block_store(), commitment)
        }
    }
}
