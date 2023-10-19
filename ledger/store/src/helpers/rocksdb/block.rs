// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{
    helpers::rocksdb::{
        internal::{self, DataMap, Database},
        BlockMap,
        MapID,
        TransactionDB,
        TransitionDB,
    },
    BlockStorage,
    ConfirmedTxType,
    TransactionStore,
    TransitionStore,
};
use console::{prelude::*, types::Field};
use ledger_authority::Authority;
use ledger_block::{Header, Ratifications};
use ledger_coinbase::{CoinbaseSolution, PuzzleCommitment};

/// A RocksDB block storage.
#[derive(Clone)]
pub struct BlockDB<N: Network> {
    /// The mapping of `block height` to `state root`.
    state_root_map: DataMap<u32, N::StateRoot>,
    /// The mapping of `state root` to `block height`.
    reverse_state_root_map: DataMap<N::StateRoot, u32>,
    /// The mapping of `block height` to `block hash`.
    id_map: DataMap<u32, N::BlockHash>,
    /// The mapping of `block hash` to `block height`.
    reverse_id_map: DataMap<N::BlockHash, u32>,
    /// The header map.
    header_map: DataMap<N::BlockHash, Header<N>>,
    /// The authority map.
    authority_map: DataMap<N::BlockHash, Authority<N>>,
    /// The certificate map.
    certificate_map: DataMap<Field<N>, (u32, u64)>,
    /// The ratifications map.
    ratifications_map: DataMap<N::BlockHash, Ratifications<N>>,
    /// The solutions map.
    solutions_map: DataMap<N::BlockHash, Option<CoinbaseSolution<N>>>,
    /// The puzzle commitments map.
    puzzle_commitments_map: DataMap<PuzzleCommitment<N>, u32>,
    /// The transactions map.
    transactions_map: DataMap<N::BlockHash, Vec<N::TransactionID>>,
    /// The aborted transaction IDs map.
    aborted_transaction_ids_map: DataMap<N::BlockHash, Vec<N::TransactionID>>,
    /// The rejected or aborted transaction ID map.
    rejected_or_aborted_transaction_id_map: DataMap<N::TransactionID, N::BlockHash>,
    /// The confirmed transactions map.
    confirmed_transactions_map: DataMap<N::TransactionID, (N::BlockHash, ConfirmedTxType, Vec<u8>)>,
    /// The transaction store.
    transaction_store: TransactionStore<N, TransactionDB<N>>,
}

#[rustfmt::skip]
impl<N: Network> BlockStorage<N> for BlockDB<N> {
    type StateRootMap = DataMap<u32, N::StateRoot>;
    type ReverseStateRootMap = DataMap<N::StateRoot, u32>;
    type IDMap = DataMap<u32, N::BlockHash>;
    type ReverseIDMap = DataMap<N::BlockHash, u32>;
    type HeaderMap = DataMap<N::BlockHash, Header<N>>;
    type AuthorityMap = DataMap<N::BlockHash, Authority<N>>;
    type CertificateMap = DataMap<Field<N>, (u32, u64)>;
    type RatificationsMap = DataMap<N::BlockHash, Ratifications<N>>;
    type SolutionsMap = DataMap<N::BlockHash, Option<CoinbaseSolution<N>>>;
    type PuzzleCommitmentsMap = DataMap<PuzzleCommitment<N>, u32>;
    type TransactionsMap = DataMap<N::BlockHash, Vec<N::TransactionID>>;
    type AbortedTransactionIDsMap = DataMap<N::BlockHash, Vec<N::TransactionID>>;
    type RejectedOrAbortedTransactionIDMap = DataMap<N::TransactionID, N::BlockHash>;
    type ConfirmedTransactionsMap = DataMap<N::TransactionID, (N::BlockHash, ConfirmedTxType, Vec<u8>)>;
    type TransactionStorage = TransactionDB<N>;
    type TransitionStorage = TransitionDB<N>;

    /// Initializes the block storage.
    fn open(dev: Option<u16>) -> Result<Self> {
        // Initialize the transition store.
        let transition_store = TransitionStore::<N, TransitionDB<N>>::open(dev)?;
        // Initialize the transaction store.
        let transaction_store = TransactionStore::<N, TransactionDB<N>>::open(transition_store)?;
        // Return the block storage.
        Ok(Self {
            state_root_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::StateRoot))?,
            reverse_state_root_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::ReverseStateRoot))?,
            id_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::ID))?,
            reverse_id_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::ReverseID))?,
            header_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::Header))?,
            authority_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::Authority))?,
            certificate_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::Certificate))?,
            ratifications_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::Ratifications))?,
            solutions_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::Solutions))?,
            puzzle_commitments_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::PuzzleCommitments))?,
            transactions_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::Transactions))?,
            aborted_transaction_ids_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::AbortedTransactionIDs))?,
            rejected_or_aborted_transaction_id_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::RejectedOrAbortedTransactionID))?,
            confirmed_transactions_map: internal::RocksDB::open_map(N::ID, dev, MapID::Block(BlockMap::ConfirmedTransactions))?,
            transaction_store,
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

    /// Returns the authority map.
    fn authority_map(&self) -> &Self::AuthorityMap {
        &self.authority_map
    }

    /// Returns the certificate map.
    fn certificate_map(&self) -> &Self::CertificateMap {
        &self.certificate_map
    }

    /// Returns the ratifications map.
    fn ratifications_map(&self) -> &Self::RatificationsMap {
        &self.ratifications_map
    }

    /// Returns the solutions map.
    fn solutions_map(&self) -> &Self::SolutionsMap {
        &self.solutions_map
    }

    /// Returns the puzzle commitments map.
    fn puzzle_commitments_map(&self) -> &Self::PuzzleCommitmentsMap {
        &self.puzzle_commitments_map
    }

    /// Returns the transactions map.
    fn transactions_map(&self) -> &Self::TransactionsMap {
        &self.transactions_map
    }

    /// Returns the aborted transaction IDs map.
    fn aborted_transaction_ids_map(&self) -> &Self::AbortedTransactionIDsMap {
        &self.aborted_transaction_ids_map
    }

    /// Returns the rejected or aborted transaction ID map.
    fn rejected_or_aborted_transaction_id_map(&self) -> &Self::RejectedOrAbortedTransactionIDMap {
        &self.rejected_or_aborted_transaction_id_map
    }

    /// Returns the confirmed transactions map.
    fn confirmed_transactions_map(&self) -> &Self::ConfirmedTransactionsMap {
        &self.confirmed_transactions_map
    }

    /// Returns the transaction store.
    fn transaction_store(&self) -> &TransactionStore<N, Self::TransactionStorage> {
        &self.transaction_store
    }
}
