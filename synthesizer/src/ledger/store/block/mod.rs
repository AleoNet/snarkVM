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

use crate::{
    atomic_write_batch,
    cow_to_cloned,
    cow_to_copied,
    ledger::{
        map::{memory_map::MemoryMap, Map, MapRead},
        store::{
            TransactionMemory,
            TransactionStorage,
            TransactionStore,
            TransitionMemory,
            TransitionStorage,
            TransitionStore,
        },
        Block,
        Header,
        Signature,
        Transactions,
    },
    CoinbaseSolution,
};
use console::network::prelude::*;

use anyhow::Result;
use core::marker::PhantomData;
use std::borrow::Cow;

macro_rules! bail_with_block {
    ($message:expr, $self:ident, $hash:expr) => {{
        let message = format!($message);
        anyhow::bail!("{message} for block '{:?}' ('{}')", $self.get_block_height(&$hash)?, $hash);
    }};
}

/// A trait for block storage.
pub trait BlockStorage<N: Network>: Clone + Send + Sync {
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
    /// The mapping of `block hash` to `block coinbase proof`.
    type CoinbaseProofMap: for<'a> Map<'a, N::BlockHash, Option<CoinbaseSolution<N>>>;
    /// The mapping of `block hash` to `block signature`.
    type SignatureMap: for<'a> Map<'a, N::BlockHash, Signature<N>>;

    /// Initializes the block storage.
    fn open(dev: Option<u16>) -> Result<Self>;

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
    /// Returns the coinbase proof map.
    fn coinbase_proof_map(&self) -> &Self::CoinbaseProofMap;
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
        self.id_map().start_atomic();
        self.reverse_id_map().start_atomic();
        self.header_map().start_atomic();
        self.transactions_map().start_atomic();
        self.reverse_transactions_map().start_atomic();
        self.transaction_store().start_atomic();
        self.coinbase_proof_map().start_atomic();
        self.signature_map().start_atomic();
    }

    /// Checks if an atomic batch is in progress.
    fn is_atomic_in_progress(&self) -> bool {
        self.id_map().is_atomic_in_progress()
            || self.reverse_id_map().is_atomic_in_progress()
            || self.header_map().is_atomic_in_progress()
            || self.transactions_map().is_atomic_in_progress()
            || self.reverse_transactions_map().is_atomic_in_progress()
            || self.transaction_store().is_atomic_in_progress()
            || self.coinbase_proof_map().is_atomic_in_progress()
            || self.signature_map().is_atomic_in_progress()
    }

    /// Aborts an atomic batch write operation.
    fn abort_atomic(&self) {
        self.id_map().abort_atomic();
        self.reverse_id_map().abort_atomic();
        self.header_map().abort_atomic();
        self.transactions_map().abort_atomic();
        self.reverse_transactions_map().abort_atomic();
        self.transaction_store().abort_atomic();
        self.coinbase_proof_map().abort_atomic();
        self.signature_map().abort_atomic();
    }

    /// Finishes an atomic batch write operation.
    fn finish_atomic(&self) -> Result<()> {
        self.id_map().finish_atomic()?;
        self.reverse_id_map().finish_atomic()?;
        self.header_map().finish_atomic()?;
        self.transactions_map().finish_atomic()?;
        self.reverse_transactions_map().finish_atomic()?;
        self.transaction_store().finish_atomic()?;
        self.coinbase_proof_map().finish_atomic()?;
        self.signature_map().finish_atomic()
    }

    /// Stores the given `block` into storage.
    fn insert(&self, block: &Block<N>) -> Result<()> {
        atomic_write_batch!(self, {
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

            // Store the block coinbase proof.
            self.coinbase_proof_map().insert(block.hash(), block.coinbase_proof().cloned())?;

            // Store the block signature.
            self.signature_map().insert(block.hash(), *block.signature())?;

            Ok(())
        });

        Ok(())
    }

    /// Removes the block for the given `block hash`.
    fn remove(&self, block_hash: &N::BlockHash) -> Result<()> {
        // Retrieve the block height.
        let height = match self.get_block_height(block_hash)? {
            Some(height) => height,
            None => bail!("Failed to remove block: missing block height for block hash '{block_hash}'"),
        };
        // Retrieve the transaction IDs.
        let transaction_ids = match self.transactions_map().get(block_hash)? {
            Some(transaction_ids) => transaction_ids,
            None => bail!("Failed to remove block: missing transactions for block '{height}' ('{block_hash}')"),
        };

        atomic_write_batch!(self, {
            // Remove the block hash.
            self.id_map().remove(&height)?;
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

            // Remove the block coinbase proof.
            self.coinbase_proof_map().remove(block_hash)?;

            // Remove the block signature.
            self.signature_map().remove(block_hash)?;

            Ok(())
        });

        Ok(())
    }

    /// Returns the block hash that contains the given `transaction ID`.
    fn find_block_hash(&self, transaction_id: &N::TransactionID) -> Result<Option<N::BlockHash>> {
        match self.reverse_transactions_map().get(transaction_id)? {
            Some(block_hash) => Ok(Some(cow_to_copied!(block_hash))),
            None => Ok(None),
        }
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

    /// Returns the block signature for the given `block hash`.
    fn get_block_signature(&self, block_hash: &N::BlockHash) -> Result<Option<Signature<N>>> {
        match self.signature_map().get(block_hash)? {
            Some(signature) => Ok(Some(cow_to_cloned!(signature))),
            None => Ok(None),
        }
    }

    /// Returns the block coinbase proof for the given `block hash`.
    fn get_block_coinbase_proof(&self, block_hash: &N::BlockHash) -> Result<Option<CoinbaseSolution<N>>> {
        match self.coinbase_proof_map().get(block_hash)? {
            Some(coinbase_proof) => Ok(cow_to_cloned!(coinbase_proof)),
            None => bail!("Missing coinbase proof for block ('{block_hash}')"),
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
        // Retrieve the block coinbase proof.
        let coinbase_proof = match self.get_block_coinbase_proof(block_hash) {
            Ok(coinbase_proof) => coinbase_proof,
            Err(_) => bail!("Missing coinbase proof for block {height} ('{block_hash}')"),
        };
        // Retrieve the block signature.
        let signature = match self.get_block_signature(block_hash)? {
            Some(signature) => signature,
            None => bail!("Missing signature for block {height} ('{block_hash}')"),
        };

        // Return the block.
        Ok(Some(Block::from(previous_hash, header, transactions, coinbase_proof, signature)?))
    }
}

/// An in-memory block storage.
#[derive(Clone)]
pub struct BlockMemory<N: Network> {
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
    /// The coinbase proof map.
    coinbase_proof_map: MemoryMap<N::BlockHash, Option<CoinbaseSolution<N>>>,
    /// The signature map.
    signature_map: MemoryMap<N::BlockHash, Signature<N>>,
}

#[rustfmt::skip]
impl<N: Network> BlockStorage<N> for BlockMemory<N> {
    type IDMap = MemoryMap<u32, N::BlockHash>;
    type ReverseIDMap = MemoryMap<N::BlockHash, u32>;
    type HeaderMap = MemoryMap<N::BlockHash, Header<N>>;
    type TransactionsMap = MemoryMap<N::BlockHash, Vec<N::TransactionID>>;
    type ReverseTransactionsMap = MemoryMap<N::TransactionID, N::BlockHash>;
    type TransactionStorage = TransactionMemory<N>;
    type TransitionStorage = TransitionMemory<N>;
    type CoinbaseProofMap = MemoryMap<N::BlockHash, Option<CoinbaseSolution<N>>>;
    type SignatureMap = MemoryMap<N::BlockHash, Signature<N>>;

    /// Initializes the block storage.
    fn open(dev: Option<u16>) -> Result<Self> {
        // Initialize the transition store.
        let transition_store = TransitionStore::<N, TransitionMemory<N>>::open(dev)?;
        // Initialize the transaction store.
        let transaction_store = TransactionStore::<N, TransactionMemory<N>>::open(transition_store)?;
        // Return the block storage.
        Ok(Self {
            id_map: MemoryMap::default(),
            reverse_id_map: MemoryMap::default(),
            header_map: MemoryMap::default(),
            transactions_map: MemoryMap::default(),
            reverse_transactions_map: MemoryMap::default(),
            transaction_store,
            coinbase_proof_map: MemoryMap::default(),
            signature_map: MemoryMap::default(),
        })
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

    /// Returns the coinbase proof map.
    fn coinbase_proof_map(&self) -> &Self::CoinbaseProofMap {
        &self.coinbase_proof_map
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
    /// PhantomData.
    _phantom: PhantomData<N>,
}

impl<N: Network, B: BlockStorage<N>> BlockStore<N, B> {
    /// Initializes the block store.
    pub fn open(dev: Option<u16>) -> Result<Self> {
        // Initialize the block storage.
        let storage = B::open(dev)?;
        // Return the block store.
        Ok(Self { storage, _phantom: PhantomData })
    }

    /// Initializes a block store from storage.
    pub fn from(storage: B) -> Self {
        Self { storage, _phantom: PhantomData }
    }

    /// Stores the given `block` into storage.
    pub fn insert(&self, block: &Block<N>) -> Result<()> {
        self.storage.insert(block)
    }

    /// Removes the block for the given `block hash`.
    pub fn remove(&self, block_hash: &N::BlockHash) -> Result<()> {
        self.storage.remove(block_hash)
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

    /// Aborts an atomic batch write operation.
    pub fn abort_atomic(&self) {
        self.storage.abort_atomic();
    }

    /// Finishes an atomic batch write operation.
    pub fn finish_atomic(&self) -> Result<()> {
        self.storage.finish_atomic()
    }
}

impl<N: Network, B: BlockStorage<N>> BlockStore<N, B> {
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

    /// Returns the block coinbase proof for the given `block hash`.
    pub fn get_block_coinbase_proof(&self, block_hash: &N::BlockHash) -> Result<Option<CoinbaseSolution<N>>> {
        self.storage.get_block_coinbase_proof(block_hash)
    }

    /// Returns the block signature for the given `block hash`.
    pub fn get_block_signature(&self, block_hash: &N::BlockHash) -> Result<Option<Signature<N>>> {
        self.storage.get_block_signature(block_hash)
    }

    /// Returns the block for the given `block hash`.
    pub fn get_block(&self, block_hash: &N::BlockHash) -> Result<Option<Block<N>>> {
        self.storage.get_block(block_hash)
    }
}

impl<N: Network, B: BlockStorage<N>> BlockStore<N, B> {
    /// Returns the block hash that contains the given `transaction ID`.
    pub fn find_block_hash(&self, transaction_id: &N::TransactionID) -> Result<Option<N::BlockHash>> {
        self.storage.find_block_hash(transaction_id)
    }
}

impl<N: Network, B: BlockStorage<N>> BlockStore<N, B> {
    /// Returns `true` if the given block height exists.
    pub fn contains_block_height(&self, height: u32) -> Result<bool> {
        self.storage.id_map().contains_key(&height)
    }

    /// Returns `true` if the given block hash exists.
    pub fn contains_block_hash(&self, block_hash: &N::BlockHash) -> Result<bool> {
        self.storage.reverse_id_map().contains_key(block_hash)
    }
}

impl<N: Network, B: BlockStorage<N>> BlockStore<N, B> {
    /// Returns an iterator over the block heights, for all blocks in `self`.
    pub fn heights(&self) -> impl '_ + Iterator<Item = Cow<'_, u32>> {
        self.storage.id_map().keys()
    }

    /// Returns an iterator over the block hashes, for all blocks in `self`.
    pub fn hashes(&self) -> impl '_ + Iterator<Item = Cow<'_, N::BlockHash>> {
        self.storage.reverse_id_map().keys()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_insert_get_remove() {
        let mut rng = TestRng::default();

        // Sample the block.
        let block = crate::ledger::test_helpers::sample_genesis_block(&mut rng);
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
        block_store.remove(&block_hash).unwrap();

        // Ensure the block does not exist.
        let candidate = block_store.get_block(&block_hash).unwrap();
        assert_eq!(None, candidate);
    }

    #[test]
    fn test_find_block_hash() {
        let mut rng = TestRng::default();

        // Sample the block.
        let block = crate::ledger::test_helpers::sample_genesis_block(&mut rng);
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
        block_store.remove(&block_hash).unwrap();

        for transaction_id in block.transaction_ids() {
            // Ensure the block hash is not found.
            let candidate = block_store.find_block_hash(transaction_id).unwrap();
            assert_eq!(None, candidate);
        }
    }
}
