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

mod contains;
pub use contains::*;

mod get;
pub use get::*;

use crate::ledger::{
    map::{memory_map::MemoryMap, Map, MapRead},
    Block,
    Header,
    Signature,
};
use console::network::prelude::*;
use snarkvm_parameters::testnet3::GenesisBytes;

use anyhow::Result;
use std::borrow::Cow;

/// A trait for block storage.
pub trait BlockStorage<N: Network>: Clone {
    type HashesMap: for<'a> Map<'a, u32, N::BlockHash>;
    type HeadersMap: for<'a> Map<'a, N::BlockHash, Header<N>>;
    type TransactionsMap: for<'a> Map<'a, N::BlockHash, Vec<N::TransactionID>>;
    type SignaturesMap: for<'a> Map<'a, N::BlockHash, Signature<N>>;
}

/// An in-memory block storage.
#[derive(Clone)]
pub struct BlockMemory<N: Network>(core::marker::PhantomData<N>);

#[rustfmt::skip]
impl<N: Network> BlockStorage<N> for BlockMemory<N> {
    type HashesMap = MemoryMap<u32, N::BlockHash>;
    type HeadersMap = MemoryMap<N::BlockHash, Header<N>>;
    type TransactionsMap = MemoryMap<N::BlockHash, Vec<N::TransactionID>>;
    type SignaturesMap = MemoryMap<N::BlockHash, Signature<N>>;
}

#[derive(Clone)]
pub struct BlockStore<N: Network, B: BlockStorage<N>> {
    /// The map of block hashes.
    hashes: B::HashesMap,
    /// The map of block headers.
    headers: B::HeadersMap,
    /// The map of block transactions.
    transactions: B::TransactionsMap,
    /// The map of block signatures.
    signatures: B::SignaturesMap,
}

impl<N: Network, B: BlockStorage<N>> BlockStore<N, B> {
    /// Initializes a new instance of `BlockStore` from the given maps.
    pub fn from_maps(
        hashes: B::HashesMap,
        headers: B::HeadersMap,
        transactions: B::TransactionsMap,
        signatures: B::SignaturesMap,
    ) -> Result<Self> {
        // Initialize the ledger.
        let mut store = Self { hashes, headers, transactions, signatures };

        // If there are no blocks, add the genesis block.
        if let None = store.hashes.keys().max() {
            // Load the genesis block.
            let genesis = Block::<N>::from_bytes_le(GenesisBytes::load_bytes())?;

            // Add the genesis block.
            store.hashes.insert(genesis.height(), genesis.hash())?;
            store.headers.insert(genesis.hash(), *genesis.header())?;
            store.transactions.insert(genesis.hash(), genesis.transaction_ids().cloned().collect())?;
            store.signatures.insert(genesis.hash(), *genesis.signature())?;
        }

        Ok(store)
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
