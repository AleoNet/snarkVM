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
    helpers::rocksdb::{self, CommitteeMap, DataMap, Database, MapID, ProgramMap},
    CommitteeStorage,
    CommitteeStore,
    FinalizeStorage,
};
use console::{
    prelude::*,
    program::{Identifier, Plaintext, ProgramID, Value},
    types::Field,
};
use ledger_committee::Committee;

use indexmap::{IndexMap, IndexSet};

/// A RocksDB finalize storage.
#[derive(Clone)]
pub struct FinalizeDB<N: Network> {
    /// The committee store.
    committee_store: CommitteeStore<N, CommitteeDB<N>>,
    /// The program ID map.
    program_id_map: DataMap<ProgramID<N>, IndexSet<Identifier<N>>>,
    /// The mapping ID map.
    mapping_id_map: DataMap<(ProgramID<N>, Identifier<N>), Field<N>>,
    /// The key-value ID map.
    key_value_id_map: DataMap<Field<N>, IndexMap<Field<N>, Field<N>>>,
    /// The key map.
    key_map: DataMap<Field<N>, Plaintext<N>>,
    /// The value map.
    value_map: DataMap<Field<N>, Value<N>>,
    /// The optional development ID.
    dev: Option<u16>,
}

#[rustfmt::skip]
impl<N: Network> FinalizeStorage<N> for FinalizeDB<N> {
    type CommitteeStorage = CommitteeDB<N>;
    type ProgramIDMap = DataMap<ProgramID<N>, IndexSet<Identifier<N>>>;
    type MappingIDMap = DataMap<(ProgramID<N>, Identifier<N>), Field<N>>;
    type KeyValueIDMap = DataMap<Field<N>, IndexMap<Field<N>, Field<N>>>;
    type KeyMap = DataMap<Field<N>, Plaintext<N>>;
    type ValueMap = DataMap<Field<N>, Value<N>>;

    /// Initializes the finalize storage.
    fn open(dev: Option<u16>) -> Result<Self> {
        // Initialize the committee store.
        let committee_store = CommitteeStore::<N, CommitteeDB<N>>::open(dev)?;
        // Return the finalize storage.
        Ok(Self {
            committee_store,
            program_id_map: rocksdb::RocksDB::open_map(N::ID, dev, MapID::Program(ProgramMap::ProgramID))?,
            mapping_id_map: rocksdb::RocksDB::open_map(N::ID, dev, MapID::Program(ProgramMap::MappingID))?,
            key_value_id_map: rocksdb::RocksDB::open_map(N::ID, dev, MapID::Program(ProgramMap::KeyValueID))?,
            key_map: rocksdb::RocksDB::open_map(N::ID, dev, MapID::Program(ProgramMap::Key))?,
            value_map: rocksdb::RocksDB::open_map(N::ID, dev, MapID::Program(ProgramMap::Value))?,
            dev,
        })
    }

    /// Returns the committee store.
    fn committee_store(&self) -> &CommitteeStore<N, Self::CommitteeStorage> {
        &self.committee_store
    }

    /// Returns the program ID map.
    fn program_id_map(&self) -> &Self::ProgramIDMap {
        &self.program_id_map
    }

    /// Returns the mapping ID map.
    fn mapping_id_map(&self) -> &Self::MappingIDMap {
        &self.mapping_id_map
    }

    /// Returns the key-value ID map.
    fn key_value_id_map(&self) -> &Self::KeyValueIDMap {
        &self.key_value_id_map
    }

    /// Returns the key map.
    fn key_map(&self) -> &Self::KeyMap {
        &self.key_map
    }

    /// Returns the value map.
    fn value_map(&self) -> &Self::ValueMap {
        &self.value_map
    }

    /// Returns the optional development ID.
    fn dev(&self) -> Option<u16> {
        self.dev
    }
}

/// A RocksDB committee storage.
#[derive(Clone)]
pub struct CommitteeDB<N: Network> {
    /// The current round map.
    current_round_map: DataMap<u8, u64>,
    /// The round to height map.
    round_to_height_map: DataMap<u64, u32>,
    /// The committee map.
    committee_map: DataMap<u32, Committee<N>>,
    /// The optional development ID.
    dev: Option<u16>,
}

#[rustfmt::skip]
impl<N: Network> CommitteeStorage<N> for CommitteeDB<N> {
    type CurrentRoundMap = DataMap<u8, u64>;
    type RoundToHeightMap = DataMap<u64, u32>;
    type CommitteeMap = DataMap<u32, Committee<N>>;

    /// Initializes the committee storage.
    fn open(dev: Option<u16>) -> Result<Self> {
        Ok(Self {
            current_round_map: rocksdb::RocksDB::open_map(N::ID, dev, MapID::Committee(CommitteeMap::CurrentRound))?,
            round_to_height_map: rocksdb::RocksDB::open_map(N::ID, dev, MapID::Committee(CommitteeMap::RoundToHeight))?,
            committee_map: rocksdb::RocksDB::open_map(N::ID, dev, MapID::Committee(CommitteeMap::Committee))?,
            dev,
        })
    }

    /// Returns the current round map.
    fn current_round_map(&self) -> &Self::CurrentRoundMap {
        &self.current_round_map
    }

    /// Returns the round to height map.
    fn round_to_height_map(&self) -> &Self::RoundToHeightMap {
        &self.round_to_height_map
    }

    /// Returns the committee map.
    fn committee_map(&self) -> &Self::CommitteeMap {
        &self.committee_map
    }

    /// Returns the optional development ID.
    fn dev(&self) -> Option<u16> {
        self.dev
    }
}
