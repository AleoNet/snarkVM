// Copyright (C) 2019-2023 Aleo Systems Inc.
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

use crate::{
    atomic_write_batch,
    block::{Block, Header, Transactions},
    coinbase_puzzle::{CoinbaseSolution, PuzzleCommitment},
    cow_to_cloned,
    cow_to_copied,
    store::{
        helpers::{memory_map::MemoryMap, Map, MapRead},
        TransactionMemory,
        TransactionStorage,
        TransactionStore,
        TransitionMemory,
        TransitionStorage,
        TransitionStore,
    },
    Program,
};
use console::{
    account::Signature,
    network::prelude::*,
    program::{BlockTree, HeaderLeaf, ProgramID, StatePath},
    types::Field,
};

use anyhow::Result;
use parking_lot::RwLock;
use std::{borrow::Cow, sync::Arc};

#[cfg(not(feature = "serial"))]
use rayon::prelude::*;

macro_rules! bail_with_block {
    ($message:expr, $self:ident, $hash:expr) => {{
        let message = format!($message);
        anyhow::bail!("{message} for block '{:?}' ('{}')", $self.get_block_height(&$hash)?, $hash);
    }};
}

/// A trait for block storage.
pub trait BlockStorage<N: Network>: 'static + Clone + Send + Sync {
    /// The mapping of `block height` to `state root`.
    type StateRootMap: for<'a> Map<'a, u32, N::StateRoot>;
    /// The mapping of `state root` to `block height`.
    type ReverseStateRootMap: for<'a> Map<'a, N::StateRoot, u32>;
    /// The mapping of `block height` to `block hash`.
    type IDMap: for<'a> Map<'a, u32, N::BlockHash>;
    /// The mapping of `block hash` to `block height`.
    type ReverseIDMap: for<'a> Map<'a, N::BlockHash, u32>;
    /// The mapping of `block hash` to `block header`.
    type HeaderMap: for<'a> Map<'a, N::BlockHash, Header<N>>;
    /// The mapping of `block hash` to `[transaction ID]`.
    type TransactionsMap: for<'a> Map<'a, N::BlockHash, Vec<N::TransactionID>>;
    /// The mapping of `transaction ID` to `block hash`.
    type ReverseTransactionsMap: for<'a> Map<'a, N::TransactionID, N::BlockHash>;
    /// The transaction storage.
    type TransactionStorage: TransactionStorage<N, TransitionStorage = Self::TransitionStorage>;
    /// The transition storage.
    type TransitionStorage: TransitionStorage<N>;
    /// The mapping of `block hash` to `block coinbase solution`.
    type CoinbaseSolutionMap: for<'a> Map<'a, N::BlockHash, Option<CoinbaseSolution<N>>>;
    /// The mapping of `puzzle commitment` to `block hash`.
    type CoinbasePuzzleCommitmentMap: for<'a> Map<'a, PuzzleCommitment<N>, N::BlockHash>;
    /// The mapping of `block hash` to `block signature`.
    type SignatureMap: for<'a> Map<'a, N::BlockHash, Signature<N>>;

    /// Initializes the block storage.
    fn open(dev: Option<u16>) -> Result<Self>;

    /// Returns the state root map.
    fn state_root_map(&self) -> &Self::StateRootMap;
    /// Returns the reverse state root map.
    fn reverse_state_root_map(&self) -> &Self::ReverseStateRootMap;
    /// Returns the ID map.
    fn id_map(&self) -> &Self::IDMap;
    /// Returns the reverse ID map.
    fn reverse_id_map(&self) -> &Self::ReverseIDMap;
    /// Returns the header map.
    fn header_map(&self) -> &Self::HeaderMap;
    /// Returns the transactions map.
    fn transactions_map(&self) -> &Self::TransactionsMap;
    /// Returns the reverse transactions map.
    fn reverse_transactions_map(&self) -> &Self::ReverseTransactionsMap;
    /// Returns the transaction store.
    fn transaction_store(&self) -> &TransactionStore<N, Self::TransactionStorage>;
    /// Returns the coinbase solution map.
    fn coinbase_solution_map(&self) -> &Self::CoinbaseSolutionMap;
    /// Returns the coinbase puzzle commitment map.
    fn coinbase_puzzle_commitment_map(&self) -> &Self::CoinbasePuzzleCommitmentMap;
    /// Returns the signature map.
    fn signature_map(&self) -> &Self::SignatureMap;

    /// Returns the transition store.
    fn transition_store(&self) -> &TransitionStore<N, Self::TransitionStorage> {
        self.transaction_store().transition_store()
    }
    /// Returns the optional development ID.
    fn dev(&self) -> Option<u16> {
        debug_assert!(self.transaction_store().dev() == self.transition_store().dev());
        self.transition_store().dev()
    }

    /// Starts an atomic batch write operation.
    fn start_atomic(&self) {
        self.state_root_map().start_atomic();
        self.reverse_state_root_map().start_atomic();
        self.id_map().start_atomic();
        self.reverse_id_map().start_atomic();
        self.header_map().start_atomic();
        self.transactions_map().start_atomic();
        self.reverse_transactions_map().start_atomic();
        self.transaction_store().start_atomic();
        self.coinbase_solution_map().start_atomic();
        self.coinbase_puzzle_commitment_map().start_atomic();
        self.signature_map().start_atomic();
    }

    /// Checks if an atomic batch is in progress.
    fn is_atomic_in_progress(&self) -> bool {
        self.state_root_map().is_atomic_in_progress()
            || self.reverse_state_root_map().is_atomic_in_progress()
            || self.id_map().is_atomic_in_progress()
            || self.reverse_id_map().is_atomic_in_progress()
            || self.header_map().is_atomic_in_progress()
            || self.transactions_map().is_atomic_in_progress()
            || self.reverse_transactions_map().is_atomic_in_progress()
            || self.transaction_store().is_atomic_in_progress()
            || self.coinbase_solution_map().is_atomic_in_progress()
            || self.coinbase_puzzle_commitment_map().is_atomic_in_progress()
            || self.signature_map().is_atomic_in_progress()
    }

    /// Aborts an atomic batch write operation.
    fn abort_atomic(&self) {
        self.state_root_map().abort_atomic();
        self.reverse_state_root_map().abort_atomic();
        self.id_map().abort_atomic();
        self.reverse_id_map().abort_atomic();
        self.header_map().abort_atomic();
        self.transactions_map().abort_atomic();
        self.reverse_transactions_map().abort_atomic();
        self.transaction_store().abort_atomic();
        self.coinbase_solution_map().abort_atomic();
        self.coinbase_puzzle_commitment_map().abort_atomic();
        self.signature_map().abort_atomic();
    }

    /// Finishes an atomic batch write operation.
    fn finish_atomic(&self) -> Result<()> {
        self.state_root_map().finish_atomic()?;
        self.reverse_state_root_map().finish_atomic()?;
        self.id_map().finish_atomic()?;
        self.reverse_id_map().finish_atomic()?;
        self.header_map().finish_atomic()?;
        self.transactions_map().finish_atomic()?;
        self.reverse_transactions_map().finish_atomic()?;
        self.transaction_store().finish_atomic()?;
        self.coinbase_solution_map().finish_atomic()?;
        self.coinbase_puzzle_commitment_map().finish_atomic()?;
        self.signature_map().finish_atomic()
    }

    /// Stores the given `(state root, block)` pair into storage.
    fn insert(&self, state_root: N::StateRoot, block: &Block<N>) -> Result<()> {
        atomic_write_batch!(self, {
            // Store the (block height, state root) pair.
            self.state_root_map().insert(block.height(), state_root)?;
            // Store the (state root, block height) pair.
            self.reverse_state_root_map().insert(state_root, block.height())?;

            // Store the block hash.
            self.id_map().insert(block.height(), block.hash())?;
            // Store the block height.
            self.reverse_id_map().insert(block.hash(), block.height())?;
            // Store the block header.
            self.header_map().insert(block.hash(), *block.header())?;

            // Store the transaction IDs.
            self.transactions_map().insert(block.hash(), block.transaction_ids().copied().collect())?;

            // Store the block transactions.
            for transaction in block.transactions().values() {
                // Store the reverse transaction ID.
                self.reverse_transactions_map().insert(transaction.id(), block.hash())?;
                // Store the transaction.
                self.transaction_store().insert(transaction)?;
            }

            // Store the block coinbase solution.
            self.coinbase_solution_map().insert(block.hash(), block.coinbase().cloned())?;

            // Store the block coinbase puzzle commitment.
            if let Some(coinbase) = block.coinbase() {
                for puzzle_commitment in coinbase.partial_solutions().iter().map(|s| s.commitment()) {
                    self.coinbase_puzzle_commitment_map().insert(puzzle_commitment, block.hash())?;
                }
            }

            // Store the block signature.
            self.signature_map().insert(block.hash(), *block.signature())?;

            Ok(())
        });

        Ok(())
    }

    /// Removes the block for the given `block hash`.
    fn remove(&self, block_hash: &N::BlockHash) -> Result<()> {
        // Retrieve the block height.
        let block_height = match self.get_block_height(block_hash)? {
            Some(height) => height,
            None => bail!("Failed to remove block: missing block height for block hash '{block_hash}'"),
        };
        // Retrieve the state root.
        let state_root = match self.state_root_map().get(&block_height)? {
            Some(state_root) => cow_to_copied!(state_root),
            None => bail!("Failed to remove block: missing state root for block height '{block_height}'"),
        };
        // Retrieve the transaction IDs.
        let transaction_ids = match self.transactions_map().get(block_hash)? {
            Some(transaction_ids) => transaction_ids,
            None => bail!("Failed to remove block: missing transactions for block '{block_height}' ('{block_hash}')"),
        };
        // Retrieve the coinbase solution.
        let coinbase = match self.coinbase_solution_map().get(block_hash)? {
            Some(coinbase_solution) => cow_to_cloned!(coinbase_solution),
            None => {
                bail!("Failed to remove block: missing coinbase solution for block '{block_height}' ('{block_hash}')")
            }
        };

        atomic_write_batch!(self, {
            // Remove the (block height, state root) pair.
            self.state_root_map().remove(&block_height)?;
            // Remove the (state root, block height) pair.
            self.reverse_state_root_map().remove(&state_root)?;

            // Remove the block hash.
            self.id_map().remove(&block_height)?;
            // Remove the block height.
            self.reverse_id_map().remove(block_hash)?;
            // Remove the block header.
            self.header_map().remove(block_hash)?;

            // Remove the transaction IDs.
            self.transactions_map().remove(block_hash)?;

            // Remove the block transactions.
            for transaction_id in transaction_ids.iter() {
                // Remove the reverse transaction ID.
                self.reverse_transactions_map().remove(transaction_id)?;
                // Remove the transaction.
                self.transaction_store().remove(transaction_id)?;
            }

            // Remove the block coinbase solution.
            self.coinbase_solution_map().remove(block_hash)?;

            // Remove the block coinbase puzzle commitment.
            if let Some(coinbase) = coinbase {
                for puzzle_commitment in coinbase.partial_solutions().iter().map(|s| s.commitment()) {
                    self.coinbase_puzzle_commitment_map().remove(&puzzle_commitment)?;
                }
            }

            // Remove the block signature.
            self.signature_map().remove(block_hash)?;

            Ok(())
        });

        Ok(())
    }

    /// Returns the block height that contains the given `state root`.
    fn find_block_height_from_state_root(&self, state_root: N::StateRoot) -> Result<Option<u32>> {
        match self.reverse_state_root_map().get(&state_root)? {
            Some(block_height) => Ok(Some(cow_to_copied!(block_height))),
            None => Ok(None),
        }
    }

    /// Returns the block hash that contains the given `transaction ID`.
    fn find_block_hash(&self, transaction_id: &N::TransactionID) -> Result<Option<N::BlockHash>> {
        match self.reverse_transactions_map().get(transaction_id)? {
            Some(block_hash) => Ok(Some(cow_to_copied!(block_hash))),
            None => Ok(None),
        }
    }

    /// Returns the block hash that contains the given `puzzle commitment`.
    fn find_block_hash_from_puzzle_commitment(
        &self,
        puzzle_commitment: &PuzzleCommitment<N>,
    ) -> Result<Option<N::BlockHash>> {
        match self.coinbase_puzzle_commitment_map().get(puzzle_commitment)? {
            Some(block_hash) => Ok(Some(cow_to_copied!(block_hash))),
            None => Ok(None),
        }
    }

    /// Returns the state root that contains the given `block height`.
    fn get_state_root(&self, block_height: u32) -> Result<Option<N::StateRoot>> {
        match self.state_root_map().get(&block_height)? {
            Some(state_root) => Ok(Some(cow_to_copied!(state_root))),
            None => Ok(None),
        }
    }

    /// Returns a state path for the given `commitment`.
    fn get_state_path_for_commitment(&self, commitment: &Field<N>, block_tree: &BlockTree<N>) -> Result<StatePath<N>> {
        // Ensure the commitment exists.
        if !self.transition_store().contains_commitment(commitment)? {
            bail!("Commitment '{commitment}' does not exist");
        }

        // Find the transition that contains the commitment.
        let transition_id = self.transition_store().find_transition_id(commitment)?;
        // Find the transaction that contains the transition.
        let transaction_id = match self.transaction_store().find_transaction_id_from_transition_id(&transition_id)? {
            Some(transaction_id) => transaction_id,
            None => bail!("The transaction ID for commitment '{commitment}' is missing in storage"),
        };
        // Find the block that contains the transaction.
        let block_hash = match self.find_block_hash(&transaction_id)? {
            Some(block_hash) => block_hash,
            None => bail!("The block hash for commitment '{commitment}' is missing in storage"),
        };

        // Retrieve the transition.
        let transition = match self.transition_store().get_transition(&transition_id)? {
            Some(transition) => transition,
            None => bail!("The transition '{transition_id}' for commitment '{commitment}' is missing in storage"),
        };
        // Retrieve the block.
        let block = match self.get_block(&block_hash)? {
            Some(block) => block,
            None => bail!("The block '{block_hash}' for commitment '{commitment}' is missing in storage"),
        };

        // Construct the global state root and block path.
        let global_state_root = *block_tree.root();
        let block_path = block_tree.prove(block.height() as usize, &block.hash().to_bits_le())?;

        // Ensure the global state root exists in storage.
        if !self.reverse_state_root_map().contains_key(&global_state_root)? {
            bail!("The global state root '{global_state_root}' for commitment '{commitment}' is missing in storage");
        }

        // Construct the transition path and transaction leaf.
        let transition_leaf = transition.to_leaf(commitment, false)?;
        let transition_path = transition.to_path(&transition_leaf)?;

        // Construct the transactions path.
        let transactions = block.transactions();
        let transactions_path = match transactions.to_path(transaction_id) {
            Ok(transactions_path) => transactions_path,
            Err(_) => bail!("The transaction '{transaction_id}' for commitment '{commitment}' is not in the block"),
        };

        // Construct the transaction path and transaction leaf.
        let transaction = match transactions.get(&transaction_id) {
            Some(transaction) => transaction,
            None => bail!("The transaction '{transaction_id}' for commitment '{commitment}' is not in the block"),
        };
        let transaction_leaf = transaction.to_leaf(transition.id())?;
        let transaction_path = transaction.to_path(&transaction_leaf)?;

        // Construct the block header path.
        let block_header = block.header();
        let header_root = block_header.to_root()?;
        let header_leaf = HeaderLeaf::<N>::new(1, block_header.transactions_root());
        let header_path = block_header.to_path(&header_leaf)?;

        Ok(StatePath::from(
            global_state_root.into(),
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
        ))
    }

    /// Returns the previous block hash of the given `block height`.
    fn get_previous_block_hash(&self, height: u32) -> Result<Option<N::BlockHash>> {
        match height.is_zero() {
            true => Ok(Some(N::BlockHash::default())),
            false => match self.id_map().get(&(height - 1))? {
                Some(block_hash) => Ok(Some(cow_to_copied!(block_hash))),
                None => Ok(None),
            },
        }
    }

    /// Returns the block hash for the given `block height`.
    fn get_block_hash(&self, height: u32) -> Result<Option<N::BlockHash>> {
        match self.id_map().get(&height)? {
            Some(block_hash) => Ok(Some(cow_to_copied!(block_hash))),
            None => Ok(None),
        }
    }

    /// Returns the block height for the given `block hash`.
    fn get_block_height(&self, block_hash: &N::BlockHash) -> Result<Option<u32>> {
        match self.reverse_id_map().get(block_hash)? {
            Some(height) => Ok(Some(cow_to_copied!(height))),
            None => Ok(None),
        }
    }

    /// Returns the block header for the given `block hash`.
    fn get_block_header(&self, block_hash: &N::BlockHash) -> Result<Option<Header<N>>> {
        match self.header_map().get(block_hash)? {
            Some(header) => Ok(Some(cow_to_cloned!(header))),
            None => Ok(None),
        }
    }

    /// Returns the block transactions for the given `block hash`.
    fn get_block_transactions(&self, block_hash: &N::BlockHash) -> Result<Option<Transactions<N>>> {
        // Retrieve the transaction IDs.
        let transaction_ids = match self.transactions_map().get(block_hash)? {
            Some(transaction_ids) => transaction_ids,
            None => return Ok(None),
        };
        // Retrieve the transactions.
        let transactions = transaction_ids
            .iter()
            .map(|transaction_id| match self.transaction_store().get_transaction(transaction_id) {
                Ok(Some(transaction)) => Ok(transaction),
                Ok(None) => bail_with_block!("Missing transaction '{transaction_id}'", self, block_hash),
                Err(err) => Err(err),
            })
            .collect::<Result<Vec<_>>>()?;
        // Return the transactions.
        Ok(Some(Transactions::from(&transactions)))
    }

    /// Returns the block coinbase solution for the given `block hash`.
    fn get_block_coinbase(&self, block_hash: &N::BlockHash) -> Result<Option<CoinbaseSolution<N>>> {
        match self.coinbase_solution_map().get(block_hash)? {
            Some(coinbase_solution) => Ok(cow_to_cloned!(coinbase_solution)),
            None => bail!("Missing coinbase solution for block ('{block_hash}')"),
        }
    }

    /// Returns the block signature for the given `block hash`.
    fn get_block_signature(&self, block_hash: &N::BlockHash) -> Result<Option<Signature<N>>> {
        match self.signature_map().get(block_hash)? {
            Some(signature) => Ok(Some(cow_to_cloned!(signature))),
            None => Ok(None),
        }
    }

    /// Returns the block for the given `block hash`.
    fn get_block(&self, block_hash: &N::BlockHash) -> Result<Option<Block<N>>> {
        // Retrieve the block height.
        let height = match self.get_block_height(block_hash)? {
            Some(height) => height,
            None => return Ok(None),
        };

        // Retrieve the block header.
        let header = match self.get_block_header(block_hash)? {
            Some(header) => header,
            None => bail!("Missing block header for block {height} ('{block_hash}')"),
        };
        // Ensure the block height matches.
        if header.height() != height {
            bail!("Mismatching block height for block {height} ('{block_hash}')")
        }

        // Retrieve the previous block hash.
        let previous_hash = match self.get_previous_block_hash(height)? {
            Some(previous_block_hash) => previous_block_hash,
            None => bail!("Missing previous block hash for block {height} ('{block_hash}')"),
        };
        // Retrieve the block transactions.
        let transactions = match self.get_block_transactions(block_hash)? {
            Some(transactions) => transactions,
            None => bail!("Missing transactions for block {height} ('{block_hash}')"),
        };
        // Retrieve the block coinbase solution.
        let coinbase = match self.get_block_coinbase(block_hash) {
            Ok(coinbase_solution) => coinbase_solution,
            Err(_) => bail!("Missing coinbase solution for block {height} ('{block_hash}')"),
        };
        // Retrieve the block signature.
        let signature = match self.get_block_signature(block_hash)? {
            Some(signature) => signature,
            None => bail!("Missing signature for block {height} ('{block_hash}')"),
        };

        // Return the block.
        Ok(Some(Block::from(previous_hash, header, transactions, coinbase, signature)?))
    }
}

/// An in-memory block storage.
#[derive(Clone)]
pub struct BlockMemory<N: Network> {
    /// The mapping of `block height` to `state root`.
    state_root_map: MemoryMap<u32, N::StateRoot>,
    /// The mapping of `state root` to `block height`.
    reverse_state_root_map: MemoryMap<N::StateRoot, u32>,
    /// The mapping of `block height` to `block hash`.
    id_map: MemoryMap<u32, N::BlockHash>,
    /// The mapping of `block hash` to `block height`.
    reverse_id_map: MemoryMap<N::BlockHash, u32>,
    /// The header map.
    header_map: MemoryMap<N::BlockHash, Header<N>>,
    /// The transactions map.
    transactions_map: MemoryMap<N::BlockHash, Vec<N::TransactionID>>,
    /// The reverse transactions map.
    reverse_transactions_map: MemoryMap<N::TransactionID, N::BlockHash>,
    /// The transaction store.
    transaction_store: TransactionStore<N, TransactionMemory<N>>,
    /// The coinbase solution map.
    coinbase_solution_map: MemoryMap<N::BlockHash, Option<CoinbaseSolution<N>>>,
    /// The coinbase puzzle commitment map.
    coinbase_puzzle_commitment_map: MemoryMap<PuzzleCommitment<N>, N::BlockHash>,
    /// The signature map.
    signature_map: MemoryMap<N::BlockHash, Signature<N>>,
}

#[rustfmt::skip]
impl<N: Network> BlockStorage<N> for BlockMemory<N> {
    type StateRootMap = MemoryMap<u32, N::StateRoot>;
    type ReverseStateRootMap = MemoryMap<N::StateRoot, u32>;
    type IDMap = MemoryMap<u32, N::BlockHash>;
    type ReverseIDMap = MemoryMap<N::BlockHash, u32>;
    type HeaderMap = MemoryMap<N::BlockHash, Header<N>>;
    type TransactionsMap = MemoryMap<N::BlockHash, Vec<N::TransactionID>>;
    type ReverseTransactionsMap = MemoryMap<N::TransactionID, N::BlockHash>;
    type TransactionStorage = TransactionMemory<N>;
    type TransitionStorage = TransitionMemory<N>;
    type CoinbaseSolutionMap = MemoryMap<N::BlockHash, Option<CoinbaseSolution<N>>>;
    type CoinbasePuzzleCommitmentMap = MemoryMap<PuzzleCommitment<N>, N::BlockHash>;
    type SignatureMap = MemoryMap<N::BlockHash, Signature<N>>;

    /// Initializes the block storage.
    fn open(dev: Option<u16>) -> Result<Self> {
        // Initialize the transition store.
        let transition_store = TransitionStore::<N, TransitionMemory<N>>::open(dev)?;
        // Initialize the transaction store.
        let transaction_store = TransactionStore::<N, TransactionMemory<N>>::open(transition_store)?;
        // Return the block storage.
        Ok(Self {
            state_root_map: MemoryMap::default(),
            reverse_state_root_map: MemoryMap::default(),
            id_map: MemoryMap::default(),
            reverse_id_map: MemoryMap::default(),
            header_map: MemoryMap::default(),
            transactions_map: MemoryMap::default(),
            reverse_transactions_map: MemoryMap::default(),
            transaction_store,
            coinbase_solution_map: MemoryMap::default(),
            coinbase_puzzle_commitment_map: MemoryMap::default(),
            signature_map: MemoryMap::default(),
        })
    }

    /// Returns the state root map.
    fn state_root_map(&self) -> &Self::StateRootMap {
        &self.state_root_map
    }

    /// Returns the reverse state root map.
    fn reverse_state_root_map(&self) -> &Self::ReverseStateRootMap {
        &self.reverse_state_root_map
    }

    /// Returns the ID map.
    fn id_map(&self) -> &Self::IDMap {
        &self.id_map
    }

    /// Returns the reverse ID map.
    fn reverse_id_map(&self) -> &Self::ReverseIDMap {
        &self.reverse_id_map
    }

    /// Returns the header map.
    fn header_map(&self) -> &Self::HeaderMap {
        &self.header_map
    }

    /// Returns the transactions map.
    fn transactions_map(&self) -> &Self::TransactionsMap {
        &self.transactions_map
    }

    /// Returns the reverse transactions map.
    fn reverse_transactions_map(&self) -> &Self::ReverseTransactionsMap {
        &self.reverse_transactions_map
    }

    /// Returns the transaction store.
    fn transaction_store(&self) -> &TransactionStore<N, Self::TransactionStorage> {
        &self.transaction_store
    }

    /// Returns the coinbase solution map.
    fn coinbase_solution_map(&self) -> &Self::CoinbaseSolutionMap {
        &self.coinbase_solution_map
    }

    /// Returns the coinbase puzzle commitment map.
    fn coinbase_puzzle_commitment_map(&self) -> &Self::CoinbasePuzzleCommitmentMap {
        &self.coinbase_puzzle_commitment_map
    }

    /// Returns the signature map.
    fn signature_map(&self) -> &Self::SignatureMap {
        &self.signature_map
    }
}

/// The block store.
#[derive(Clone)]
pub struct BlockStore<N: Network, B: BlockStorage<N>> {
    /// The block storage.
    storage: B,
    /// The block tree.
    tree: Arc<RwLock<BlockTree<N>>>,
}

impl<N: Network, B: BlockStorage<N>> BlockStore<N, B> {
    /// Initializes the block store.
    pub fn open(dev: Option<u16>) -> Result<Self> {
        // Initialize the block storage.
        let storage = B::open(dev)?;

        // Compute the block tree.
        let tree = {
            // Prepare an iterator over the block heights.
            let heights = storage.id_map().keys();
            // Prepare the leaves of the block tree.
            let hashes = match heights.max() {
                Some(height) => cfg_into_iter!(0..=cow_to_copied!(height))
                    .map(|height| match storage.get_block_hash(height)? {
                        Some(hash) => Ok(hash.to_bits_le()),
                        None => bail!("Missing block hash for block {height}"),
                    })
                    .collect::<Result<Vec<Vec<bool>>>>()?,
                None => vec![],
            };
            // Construct the block tree.
            Arc::new(RwLock::new(N::merkle_tree_bhp(&hashes)?))
        };

        // Return the block store.
        Ok(Self { storage, tree })
    }

    /// Stores the given block into storage.
    pub fn insert(&self, block: &Block<N>) -> Result<()> {
        // Acquire the write lock on the block tree.
        let mut tree = self.tree.write();
        // Prepare an updated Merkle tree containing the new block hash.
        let updated_tree = tree.prepare_append(&[block.hash().to_bits_le()])?;
        // Ensure the next block height is correct.
        if block.height() != u32::try_from(updated_tree.number_of_leaves())? - 1 {
            bail!("Attempted to insert a block at the incorrect height into storage")
        }
        // Insert the (state root, block height) pair.
        self.storage.insert((*updated_tree.root()).into(), block)?;
        // Update the block tree.
        *tree = updated_tree;
        // Return success.
        Ok(())
    }

    /// Removes the last 'n' blocks from storage.
    pub fn remove_last_n(&self, n: u32) -> Result<()> {
        // Ensure 'n' is non-zero.
        ensure!(n > 0, "Cannot remove zero blocks");

        // Acquire the write lock on the block tree.
        let mut tree = self.tree.write();

        // Determine the block heights to remove.
        let heights = match self.storage.id_map().keys().max() {
            Some(height) => {
                // Determine the end block height to remove.
                let end_height = cow_to_copied!(height);
                // Determine the start block height to remove.
                let start_height = end_height
                    .checked_sub(n - 1)
                    .ok_or_else(|| anyhow!("Failed to remove last '{n}' blocks: block height underflow"))?;
                // Ensure the block height matches the number of leaves in the Merkle tree.
                ensure!(end_height == u32::try_from(tree.number_of_leaves())? - 1, "Block height mismatch");
                // Output the block heights.
                start_height..=end_height
            }
            None => bail!("Failed to remove last '{n}' blocks: no blocks in storage"),
        };

        // Fetch the block hashes to remove.
        let hashes = cfg_into_iter!(heights)
            .map(|height| match self.storage.get_block_hash(height)? {
                Some(hash) => Ok(hash),
                None => bail!("Failed to remove last '{n}' blocks: missing block hash for block {height}"),
            })
            .collect::<Result<Vec<_>>>()?;

        // Prepare an updated Merkle tree removing the last 'n' block hashes.
        let updated_tree = tree.prepare_remove_last_n(usize::try_from(n)?)?;

        atomic_write_batch!(self, {
            // Remove the blocks, in descending order.
            for block_hash in hashes.iter().rev() {
                self.storage.remove(block_hash)?;
            }
            Ok(())
        });

        // Update the block tree.
        *tree = updated_tree;
        // Return success.
        Ok(())
    }

    /// Returns the transaction store.
    pub fn transaction_store(&self) -> &TransactionStore<N, B::TransactionStorage> {
        self.storage.transaction_store()
    }

    /// Returns the transition store.
    pub fn transition_store(&self) -> &TransitionStore<N, B::TransitionStorage> {
        self.storage.transaction_store().transition_store()
    }

    /// Starts an atomic batch write operation.
    pub fn start_atomic(&self) {
        self.storage.start_atomic();
    }

    /// Checks if an atomic batch is in progress.
    pub fn is_atomic_in_progress(&self) -> bool {
        self.storage.is_atomic_in_progress()
    }

    /// Aborts an atomic batch write operation.
    pub fn abort_atomic(&self) {
        self.storage.abort_atomic();
    }

    /// Finishes an atomic batch write operation.
    pub fn finish_atomic(&self) -> Result<()> {
        self.storage.finish_atomic()
    }

    /// Returns the optional development ID.
    pub fn dev(&self) -> Option<u16> {
        self.storage.dev()
    }
}

impl<N: Network, B: BlockStorage<N>> BlockStore<N, B> {
    /// Returns the block height that contains the given `state root`.
    pub fn find_block_height_from_state_root(&self, state_root: N::StateRoot) -> Result<Option<u32>> {
        self.storage.find_block_height_from_state_root(state_root)
    }

    /// Returns the block hash that contains the given `transaction ID`.
    pub fn find_block_hash(&self, transaction_id: &N::TransactionID) -> Result<Option<N::BlockHash>> {
        self.storage.find_block_hash(transaction_id)
    }

    /// Returns the block hash that contains the given `puzzle commitment`.
    pub fn find_block_hash_from_puzzle_commitment(
        &self,
        puzzle_commitment: &PuzzleCommitment<N>,
    ) -> Result<Option<N::BlockHash>> {
        self.storage.find_block_hash_from_puzzle_commitment(puzzle_commitment)
    }
}

impl<N: Network, B: BlockStorage<N>> BlockStore<N, B> {
    /// Returns the current state root.
    pub fn current_state_root(&self) -> N::StateRoot {
        (*self.tree.read().root()).into()
    }

    /// Returns the state root that contains the given `block height`.
    pub fn get_state_root(&self, block_height: u32) -> Result<Option<N::StateRoot>> {
        self.storage.get_state_root(block_height)
    }

    /// Returns a state path for the given `commitment`.
    pub fn get_state_path_for_commitment(&self, commitment: &Field<N>) -> Result<StatePath<N>> {
        self.storage.get_state_path_for_commitment(commitment, &self.tree.read())
    }

    /// Returns the previous block hash of the given `block height`.
    pub fn get_previous_block_hash(&self, height: u32) -> Result<Option<N::BlockHash>> {
        self.storage.get_previous_block_hash(height)
    }

    /// Returns the block hash for the given `block height`.
    pub fn get_block_hash(&self, height: u32) -> Result<Option<N::BlockHash>> {
        self.storage.get_block_hash(height)
    }

    /// Returns the block height for the given `block hash`.
    pub fn get_block_height(&self, block_hash: &N::BlockHash) -> Result<Option<u32>> {
        self.storage.get_block_height(block_hash)
    }

    /// Returns the block header for the given `block hash`.
    pub fn get_block_header(&self, block_hash: &N::BlockHash) -> Result<Option<Header<N>>> {
        self.storage.get_block_header(block_hash)
    }

    /// Returns the block transactions for the given `block hash`.
    pub fn get_block_transactions(&self, block_hash: &N::BlockHash) -> Result<Option<Transactions<N>>> {
        self.storage.get_block_transactions(block_hash)
    }

    /// Returns the block coinbase solution for the given `block hash`.
    pub fn get_block_coinbase(&self, block_hash: &N::BlockHash) -> Result<Option<CoinbaseSolution<N>>> {
        self.storage.get_block_coinbase(block_hash)
    }

    /// Returns the block signature for the given `block hash`.
    pub fn get_block_signature(&self, block_hash: &N::BlockHash) -> Result<Option<Signature<N>>> {
        self.storage.get_block_signature(block_hash)
    }

    /// Returns the block for the given `block hash`.
    pub fn get_block(&self, block_hash: &N::BlockHash) -> Result<Option<Block<N>>> {
        self.storage.get_block(block_hash)
    }

    /// Returns the program for the given `program ID`.
    pub fn get_program(&self, program_id: &ProgramID<N>) -> Result<Option<Program<N>>> {
        self.storage.transaction_store().get_program(program_id)
    }
}

impl<N: Network, B: BlockStorage<N>> BlockStore<N, B> {
    /// Returns `true` if the given state root exists.
    pub fn contains_state_root(&self, state_root: &N::StateRoot) -> Result<bool> {
        self.storage.reverse_state_root_map().contains_key(state_root)
    }

    /// Returns `true` if the given block height exists.
    pub fn contains_block_height(&self, height: u32) -> Result<bool> {
        self.storage.id_map().contains_key(&height)
    }

    /// Returns `true` if the given block hash exists.
    pub fn contains_block_hash(&self, block_hash: &N::BlockHash) -> Result<bool> {
        self.storage.reverse_id_map().contains_key(block_hash)
    }

    /// Returns `true` if the given puzzle commitment exists.
    pub fn contains_puzzle_commitment(&self, puzzle_commitment: &PuzzleCommitment<N>) -> Result<bool> {
        self.storage.coinbase_puzzle_commitment_map().contains_key(puzzle_commitment)
    }
}

impl<N: Network, B: BlockStorage<N>> BlockStore<N, B> {
    /// Returns an iterator over the state roots, for all blocks in `self`.
    pub fn state_roots(&self) -> impl '_ + Iterator<Item = Cow<'_, N::StateRoot>> {
        self.storage.reverse_state_root_map().keys()
    }

    /// Returns an iterator over the block heights, for all blocks in `self`.
    pub fn heights(&self) -> impl '_ + Iterator<Item = Cow<'_, u32>> {
        self.storage.id_map().keys()
    }

    /// Returns an iterator over the block hashes, for all blocks in `self`.
    pub fn hashes(&self) -> impl '_ + Iterator<Item = Cow<'_, N::BlockHash>> {
        self.storage.reverse_id_map().keys()
    }

    /// Returns an iterator over the puzzle commitments, for all blocks in `self`.
    pub fn puzzle_commitments(&self) -> impl '_ + Iterator<Item = Cow<'_, PuzzleCommitment<N>>> {
        self.storage.coinbase_puzzle_commitment_map().keys()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_insert_get_remove() {
        let mut rng = TestRng::default();

        // Sample the block.
        let block = crate::vm::test_helpers::sample_genesis_block(&mut rng);
        let block_hash = block.hash();

        // Initialize a new block store.
        let block_store = BlockStore::<_, BlockMemory<_>>::open(None).unwrap();

        // Ensure the block does not exist.
        let candidate = block_store.get_block(&block_hash).unwrap();
        assert_eq!(None, candidate);

        // Insert the block.
        block_store.insert(&block).unwrap();

        // Retrieve the block.
        let candidate = block_store.get_block(&block_hash).unwrap();
        assert_eq!(Some(block), candidate);

        // Remove the block.
        block_store.remove_last_n(1).unwrap();

        // Ensure the block does not exist.
        let candidate = block_store.get_block(&block_hash).unwrap();
        assert_eq!(None, candidate);
    }

    #[test]
    fn test_find_block_hash() {
        let mut rng = TestRng::default();

        // Sample the block.
        let block = crate::vm::test_helpers::sample_genesis_block(&mut rng);
        let block_hash = block.hash();
        assert!(block.transactions().len() > 0, "This test must be run with at least one transaction.");

        // Initialize a new block store.
        let block_store = BlockStore::<_, BlockMemory<_>>::open(None).unwrap();

        // Ensure the block does not exist.
        let candidate = block_store.get_block(&block_hash).unwrap();
        assert_eq!(None, candidate);

        for transaction_id in block.transaction_ids() {
            // Ensure the block hash is not found.
            let candidate = block_store.find_block_hash(transaction_id).unwrap();
            assert_eq!(None, candidate);
        }

        // Insert the block.
        block_store.insert(&block).unwrap();

        for transaction_id in block.transaction_ids() {
            // Find the block hash.
            let candidate = block_store.find_block_hash(transaction_id).unwrap();
            assert_eq!(Some(block_hash), candidate);
        }

        // Remove the block.
        block_store.remove_last_n(1).unwrap();

        for transaction_id in block.transaction_ids() {
            // Ensure the block hash is not found.
            let candidate = block_store.find_block_hash(transaction_id).unwrap();
            assert_eq!(None, candidate);
        }
    }
}
