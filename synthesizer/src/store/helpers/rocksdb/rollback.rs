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
    store::{
        helpers::rocksdb::{self, DataMap, Database, MapID, RollbackMap},
        RollbackStorage,
    },
    RollbackOperation,
};
use console::prelude::*;

/// A RocksDB rollback storage.
#[derive(Clone)]
pub struct RollbackDB<N: Network> {
    /// The rollback map.
    rollback_map: DataMap<N::TransactionID, Vec<RollbackOperation<N>>>,
    /// The optional development ID.
    dev: Option<u16>,
}

#[rustfmt::skip]
impl<N: Network> RollbackStorage<N> for RollbackDB<N> {
    type RollbackMap = DataMap<N::TransactionID, Vec<RollbackOperation<N>>>;

    /// Initializes the rollback storage.
    fn open(dev: Option<u16>) -> Result<Self> {
        Ok(Self {
            rollback_map: rocksdb::RocksDB::open_map(N::ID, dev, MapID::Rollback(RollbackMap::RollBack))?,
            dev,
        })
    }

    /// Returns the rollback map.
    fn rollback_map(&self) -> &Self::RollbackMap {
        &self.rollback_map
    }

    /// Returns the optional development ID.
    fn dev(&self) -> Option<u16> {
        self.dev
    }
}
