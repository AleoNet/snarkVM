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
pub trait BlockStorage<N: Network>: Clone {
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
    /// The mapping of `block hash` to `block signature`.
    type SignatureMap: for<'a> Map<'a, N::BlockHash, Signature<N>>;

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
    /// Returns the signature map.
    fn signature_map(&self) -> &Self::SignatureMap;

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
        // Retrieve the block signature.
        let signature = match self.get_block_signature(block_hash)? {
            Some(signature) => signature,
            None => bail!("Missing signature for block {height} ('{block_hash}')"),
        };

        // Return the block.
        Ok(Some(Block::from(previous_hash, header, transactions, signature)?))
    }

    /// Stores the given `block` into storage.
    fn insert(&self, block: &Block<N>) -> Result<()> {
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

        // Store the block signature.
        self.signature_map().insert(block.hash(), *block.signature())?;

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

        // Remove the block signature.
        self.signature_map().remove(block_hash)?;

        Ok(())
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
    /// The signature map.
    signature_map: MemoryMap<N::BlockHash, Signature<N>>,
}

impl<N: Network> BlockMemory<N> {
    /// Creates a new in-memory block storage.
    pub fn new(transaction_store: TransactionStore<N, TransactionMemory<N>>) -> Self {
        Self {
            id_map: MemoryMap::default(),
            reverse_id_map: MemoryMap::default(),
            header_map: MemoryMap::default(),
            transactions_map: MemoryMap::default(),
            reverse_transactions_map: MemoryMap::default(),
            transaction_store,
            signature_map: MemoryMap::default(),
        }
    }
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
    type SignatureMap = MemoryMap<N::BlockHash, Signature<N>>;

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
    /// Initializes a new block store.
    pub fn new(storage: B) -> Self {
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
        &self.storage.transaction_store()
    }

    /// Returns the transition store.
    pub fn transition_store(&self) -> &TransitionStore<N, B::TransitionStorage> {
        &self.storage.transaction_store().transition_store()
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

// /// Checks the given transaction is well formed and unique.
// pub fn check_transaction(&self, transaction: &Transaction<N>) -> Result<()> {
//     let transaction_id = transaction.id();
//     if self.contains_transaction_id(&transaction_id)? {
//         bail!("Transaction '{transaction_id}' already exists in the ledger")
//     }
//
//     // Ensure the ledger does not already contain a given transition public keys.
//     for tpk in transaction.transition_public_keys() {
//         if self.contains_transition_public_key(tpk)? {
//             bail!("Transition public key '{tpk}' already exists in the ledger")
//         }
//     }
//
//     // Ensure that the origin are valid.
//     for origin in transaction.origins() {
//         if !self.contains_origin(origin)? {
//             bail!("The given transaction references a non-existent origin {}", &origin)
//         }
//
//         match origin {
//             // Check that the commitment exists in the ledger.
//             Origin::Commitment(commitment) => {
//                 if !self.contains_commitment(commitment)? {
//                     bail!("The given transaction references a non-existent commitment {}", &commitment)
//                 }
//             }
//             // TODO (raychu86): Ensure that the state root exists in the ledger.
//             // Check that the state root is an existing state root.
//             Origin::StateRoot(_state_root) => {
//                 bail!("State roots are currently not supported (yet)")
//             }
//         }
//     }
//
//     // Ensure the ledger does not already contain a given serial numbers.
//     for serial_number in transaction.serial_numbers() {
//         if self.contains_serial_number(serial_number)? {
//             bail!("Serial number '{serial_number}' already exists in the ledger")
//         }
//     }
//
//     // Ensure the ledger does not already contain a given commitments.
//     for commitment in transaction.commitments() {
//         if self.contains_commitment(commitment)? {
//             bail!("Commitment '{commitment}' already exists in the ledger")
//         }
//     }
//
//     // Ensure the ledger does not already contain a given nonces.
//     for nonce in transaction.nonces() {
//         if self.contains_nonce(nonce)? {
//             bail!("Nonce '{nonce}' already exists in the ledger")
//         }
//     }
//
//     Ok(())
// }
//
// /// Adds the given transaction to the transaction store.
// pub fn insert(&mut self, transaction: Transaction<N>) -> Result<()> {
//     // Check that there are not collisions with existing transactions.
//     self.check_transaction(&transaction)?;
//
//     /* ATOMIC CODE SECTION */
//
//     // Insert the transaction. This code section executes atomically.
//     {
//         let mut transaction_store = self.clone();
//
//         for transition in transaction.transitions() {
//             let transition_id = transition.id();
//
//             // Insert the transitions.
//             transaction_store.transitions.insert(*transition_id, transition.clone())?;
//
//             // Insert the transition public key.
//             transaction_store.transition_public_keys.insert(*transition.tpk(), *transition_id)?;
//
//             // Insert the serial numbers.
//             for serial_number in transition.serial_numbers() {
//                 transaction_store.serial_numbers.insert(*serial_number, *transition_id)?;
//             }
//
//             // Insert the commitments.
//             for commitment in transition.commitments() {
//                 transaction_store.commitments.insert(*commitment, *transition_id)?;
//             }
//
//             // Insert the origins.
//             for origin in transition.origins() {
//                 transaction_store.origins.insert(*origin, *transition_id)?;
//             }
//
//             // Insert the nonces.
//             for nonce in transition.nonces() {
//                 transaction_store.nonces.insert(*nonce, *transition_id)?;
//             }
//         }
//
//         // Insert the deployment or execution.
//         match transaction {
//             Transaction::Deploy(transaction_id, deployment, additional_fee) => {
//                 transaction_store.deployments.insert(transaction_id, (deployment, *additional_fee.id()))?;
//             }
//             Transaction::Execute(transaction_id, execution, additional_fee) => {
//                 let transition_ids = execution.iter().map(|transition| *transition.id()).collect();
//
//                 transaction_store
//                     .executions
//                     .insert(transaction_id, (transition_ids, additional_fee.map(|t| *t.id())))?;
//             }
//         }
//
//         *self = Self {
//             deployments: transaction_store.deployments,
//             executions: transaction_store.executions,
//             transitions: transaction_store.transitions,
//             transition_public_keys: transaction_store.transition_public_keys,
//             origins: transaction_store.origins,
//             serial_numbers: transaction_store.serial_numbers,
//             commitments: transaction_store.commitments,
//             nonces: transaction_store.nonces,
//         };
//     }
//
//     Ok(())
// }
