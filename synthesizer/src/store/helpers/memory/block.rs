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
    block::Header,
    coinbase_puzzle::{CoinbaseSolution, PuzzleCommitment},
    store::{
        helpers::memory::{MemoryMap, TransactionMemory, TransitionMemory},
        BlockStorage,
        ConfirmedTxType,
        TransactionStore,
        TransitionStore,
    },
};
use console::{account::Signature, prelude::*};

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
    /// The confirmed transactions map.
    confirmed_transactions_map: MemoryMap<N::TransactionID, (N::BlockHash, ConfirmedTxType, Vec<u8>)>,
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
    type ConfirmedTransactionsMap = MemoryMap<N::TransactionID, (N::BlockHash, ConfirmedTxType, Vec<u8>)>;
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
            confirmed_transactions_map: MemoryMap::default(),
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

    /// Returns the confirmed transactions map.
    fn confirmed_transactions_map(&self) -> &Self::ConfirmedTransactionsMap {
        &self.confirmed_transactions_map
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
