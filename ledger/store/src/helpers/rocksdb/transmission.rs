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

#![allow(clippy::type_complexity)]

use crate::{
    helpers::rocksdb::{self, Database, MapID, NestedDataMap, TransmissionMap},
    TransmissionStorage,
};
use console::prelude::*;
use ledger_narwhal_transmission::Transmission;
use ledger_narwhal_transmission_id::TransmissionID;

/// A RocksDB finalize storage.
#[derive(Clone)]
pub struct TransmissionDB<N: Network> {
    /// The transmission map.
    transmission_map: NestedDataMap<u64, TransmissionID<N>, Transmission<N>>,
    /// The optional development ID.
    dev: Option<u16>,
}

#[rustfmt::skip]
impl<N: Network> TransmissionStorage<N> for TransmissionDB<N> {
    type TransmissionMap = NestedDataMap<u64, TransmissionID<N>, Transmission<N>>;

    /// Initializes the transmission storage.
    fn open(dev: Option<u16>) -> Result<Self> {
        // Return the transmission storage.
        Ok(Self {
            transmission_map: rocksdb::RocksDB::open_nested_map(N::ID, dev, MapID::Transmission(TransmissionMap::ID))?,
            dev,
        })
    }

    /// Initializes the test-variant of the storage.
    #[cfg(any(test, feature = "test"))]
    fn open_testing(temp_dir: std::path::PathBuf, dev: Option<u16>) -> Result<Self> {
        Ok(Self {
            transmission_map: rocksdb::RocksDB::open_nested_map_testing(temp_dir.clone(), dev, MapID::Transmission(TransmissionMap::ID))?,
            dev,
        })
    }
    /// Returns the committee store.
    fn transmission_map(&self) -> &Self::TransmissionMap {
        &self.transmission_map
    }

    /// Returns the optional development ID.
    fn dev(&self) -> Option<u16> {
        self.dev
    }
}
