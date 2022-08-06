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
