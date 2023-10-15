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

mod id;
pub use id::*;

mod map;
pub use map::*;

mod nested_map;
pub use nested_map::*;

#[cfg(test)]
mod tests;

use anyhow::{bail, Result};
use once_cell::sync::OnceCell;
use parking_lot::Mutex;
use serde::{de::DeserializeOwned, Serialize};
use std::{
    borrow::Borrow,
    marker::PhantomData,
    ops::Deref,
    sync::{
        atomic::{AtomicBool, AtomicUsize},
        Arc,
    },
};

pub const PREFIX_LEN: usize = 4; // N::ID (u16) + DataID (u16)

pub trait Database {
    /// Opens the database.
    fn open(network_id: u16, dev: Option<u16>) -> Result<Self>
    where
        Self: Sized;

    /// Opens the map with the given `network_id`, `(optional) development ID`, and `map_id` from storage.
    fn open_map<K: Serialize + DeserializeOwned, V: Serialize + DeserializeOwned, T: Into<u16>>(
        network_id: u16,
        dev: Option<u16>,
        map_id: T,
    ) -> Result<DataMap<K, V>>;

    /// Opens the nested map with the given `network_id`, `(optional) development ID`, and `map_id` from storage.
    fn open_nested_map<
        M: Serialize + DeserializeOwned,
        K: Serialize + DeserializeOwned,
        V: Serialize + DeserializeOwned,
        T: Into<u16>,
    >(
        network_id: u16,
        dev: Option<u16>,
        map_id: T,
    ) -> Result<NestedDataMap<M, K, V>>;
}

/// An instance of a RocksDB database.
#[derive(Clone)]
pub struct RocksDB {
    /// The RocksDB instance.
    rocksdb: Arc<rocksdb::DB>,
    /// The network ID.
    network_id: u16,
    /// The optional development ID.
    dev: Option<u16>,
    /// The low-level database transaction that gets executed atomically at the end
    /// of a real-run `atomic_finalize` or the outermost `atomic_batch_scope`.
    pub(super) atomic_batch: Arc<Mutex<rocksdb::WriteBatch>>,
    /// The depth of the current atomic write batch; it gets incremented with every call
    /// to `start_atomic` and decremented with each call to `finish_atomic`.
    pub(super) atomic_depth: Arc<AtomicUsize>,
}

impl Deref for RocksDB {
    type Target = Arc<rocksdb::DB>;

    fn deref(&self) -> &Self::Target {
        &self.rocksdb
    }
}

impl Database for RocksDB {
    /// Opens the database.
    ///
    /// In production mode, the database opens directory `~/.aleo/storage/ledger-{network}`.
    /// In development mode, the database opens directory `/path/to/repo/.ledger-{network}-{id}`.
    fn open(network_id: u16, dev: Option<u16>) -> Result<Self> {
        static DB: OnceCell<RocksDB> = OnceCell::new();

        // Retrieve the database.
        let database = DB
            .get_or_try_init(|| {
                // Customize database options.
                let mut options = rocksdb::Options::default();
                options.set_compression_type(rocksdb::DBCompressionType::Lz4);

                // Register the prefix length.
                let prefix_extractor = rocksdb::SliceTransform::create_fixed_prefix(PREFIX_LEN);
                options.set_prefix_extractor(prefix_extractor);

                let primary = aleo_std::aleo_ledger_dir(network_id, dev);
                let rocksdb = {
                    options.increase_parallelism(2);
                    options.set_max_background_jobs(4);
                    options.create_if_missing(true);

                    Arc::new(rocksdb::DB::open(&options, primary)?)
                };

                Ok::<_, anyhow::Error>(RocksDB {
                    rocksdb,
                    network_id,
                    dev,
                    atomic_batch: Default::default(),
                    atomic_depth: Default::default(),
                })
            })?
            .clone();

        // Ensure the database network ID and development ID match.
        match database.network_id == network_id && database.dev == dev {
            true => Ok(database),
            false => bail!("Mismatching network ID or development ID in the database"),
        }
    }

    /// Opens the map with the given `network_id`, `(optional) development ID`, and `map_id` from storage.
    fn open_map<K: Serialize + DeserializeOwned, V: Serialize + DeserializeOwned, T: Into<u16>>(
        network_id: u16,
        dev: Option<u16>,
        map_id: T,
    ) -> Result<DataMap<K, V>> {
        // Open the RocksDB database.
        let database = Self::open(network_id, dev)?;

        // Combine contexts to create a new scope.
        let mut context = database.network_id.to_le_bytes().to_vec();
        context.extend_from_slice(&(map_id.into()).to_le_bytes());

        // Return the DataMap.
        Ok(DataMap(Arc::new(InnerDataMap {
            database,
            context,
            batch_in_progress: Default::default(),
            atomic_batch: Default::default(),
            checkpoints: Default::default(),
        })))
    }

    /// Opens the nested map with the given `network_id`, `(optional) development ID`, and `map_id` from storage.
    fn open_nested_map<
        M: Serialize + DeserializeOwned,
        K: Serialize + DeserializeOwned,
        V: Serialize + DeserializeOwned,
        T: Into<u16>,
    >(
        network_id: u16,
        dev: Option<u16>,
        map_id: T,
    ) -> Result<NestedDataMap<M, K, V>> {
        // Open the RocksDB database.
        let database = Self::open(network_id, dev)?;

        // Combine contexts to create a new scope.
        let mut context = database.network_id.to_le_bytes().to_vec();
        context.extend_from_slice(&(map_id.into()).to_le_bytes());

        // Return the DataMap.
        Ok(NestedDataMap {
            database,
            context,
            batch_in_progress: Default::default(),
            atomic_batch: Default::default(),
            checkpoints: Default::default(),
        })
    }
}

impl RocksDB {
    /// Opens the test database.
    #[cfg(any(test, feature = "test"))]
    pub fn open_testing(temp_dir: std::path::PathBuf, dev: Option<u16>) -> Result<Self> {
        use console::prelude::{Rng, TestRng};

        let database = {
            // Customize database options.
            let mut options = rocksdb::Options::default();
            options.set_compression_type(rocksdb::DBCompressionType::Lz4);

            // Register the prefix length.
            let prefix_extractor = rocksdb::SliceTransform::create_fixed_prefix(PREFIX_LEN);
            options.set_prefix_extractor(prefix_extractor);

            // Ensure the `temp_dir` is unique.
            let temp_dir = temp_dir.join(Rng::gen::<u64>(&mut TestRng::default()).to_string());

            // Construct the directory for the test database.
            let primary = match dev {
                Some(dev) => temp_dir.join(dev.to_string()),
                None => temp_dir,
            };

            let rocksdb = {
                options.increase_parallelism(2);
                options.set_max_background_jobs(4);
                options.create_if_missing(true);

                // Keep these around as options for configuration testing.

                // options.set_max_subcompactions(4);
                // options.set_use_direct_io_for_flush_and_compaction(true);
                // options.set_bytes_per_sync(1 << 28);
                // options.set_compaction_readahead_size(1 << 28);
                // options.set_max_write_buffer_number(16);
                // options.set_min_write_buffer_number_to_merge(8);
                // options.set_compression_type(rocksdb::DBCompressionType::None);
                // options.set_bottommost_compression_type(rocksdb::DBCompressionType::None);
                // options.set_write_buffer_size(1 << 28);

                Arc::new(rocksdb::DB::open(&options, primary)?)
            };

            Ok::<_, anyhow::Error>(RocksDB {
                rocksdb,
                network_id: u16::MAX,
                dev,
                atomic_batch: Default::default(),
                atomic_depth: Default::default(),
            })
        }?;

        // Ensure the database development ID match.
        match database.dev == dev {
            true => Ok(database),
            false => bail!("Mismatching development ID in the test database"),
        }
    }

    /// Opens the test map.
    #[cfg(any(test, feature = "test"))]
    pub fn open_map_testing<K: Serialize + DeserializeOwned, V: Serialize + DeserializeOwned, T: Into<u16>>(
        temp_dir: std::path::PathBuf,
        dev: Option<u16>,
        map_id: T,
    ) -> Result<DataMap<K, V>> {
        // Open the RocksDB test database.
        let database = Self::open_testing(temp_dir, dev)?;

        // Combine contexts to create a new scope.
        let mut context = database.network_id.to_le_bytes().to_vec();
        context.extend_from_slice(&(map_id.into()).to_le_bytes());

        // Return the DataMap.
        Ok(DataMap(Arc::new(InnerDataMap {
            database,
            context,
            batch_in_progress: Default::default(),
            atomic_batch: Default::default(),
            checkpoints: Default::default(),
        })))
    }

    /// Opens the test nested map.
    #[cfg(any(test, feature = "test"))]
    pub fn open_nested_map_testing<
        M: Serialize + DeserializeOwned,
        K: Serialize + DeserializeOwned,
        V: Serialize + DeserializeOwned,
        T: Into<u16>,
    >(
        temp_dir: std::path::PathBuf,
        dev: Option<u16>,
        map_id: T,
    ) -> Result<NestedDataMap<M, K, V>> {
        // Open the RocksDB test database.
        let database = Self::open_testing(temp_dir, dev)?;

        // Combine contexts to create a new scope.
        let mut context = database.network_id.to_le_bytes().to_vec();
        context.extend_from_slice(&(map_id.into()).to_le_bytes());

        // Return the DataMap.
        Ok(NestedDataMap {
            database,
            context,
            batch_in_progress: Default::default(),
            atomic_batch: Default::default(),
            checkpoints: Default::default(),
        })
    }
}

// impl RocksDB {
//     /// Imports a file with the given path to reconstruct storage.
//     fn import<P: AsRef<Path>>(&self, path: P) -> Result<()> {
//         let file = File::open(path)?;
//         let mut reader = BufReader::new(file);
//
//         let len = reader.seek(SeekFrom::End(0))?;
//         reader.rewind()?;
//
//         let mut buf = vec![0u8; 16 * 1024];
//
//         while reader.stream_position()? < len {
//             reader.read_exact(&mut buf[..4])?;
//             let key_len = u32::from_le_bytes(buf[..4].try_into().unwrap()) as usize;
//
//             if key_len + 4 > buf.len() {
//                 buf.resize(key_len + 4, 0);
//             }
//
//             reader.read_exact(&mut buf[..key_len + 4])?;
//             let value_len = u32::from_le_bytes(buf[key_len..][..4].try_into().unwrap()) as usize;
//
//             if key_len + value_len > buf.len() {
//                 buf.resize(key_len + value_len, 0);
//             }
//
//             reader.read_exact(&mut buf[key_len..][..value_len])?;
//
//             self.rocksdb.put(&buf[..key_len], &buf[key_len..][..value_len])?;
//         }
//
//         Ok(())
//     }
//
//     /// Exports the current state of storage to a single file at the specified location.
//     fn export<P: AsRef<Path>>(&self, path: P) -> Result<()> {
//         let file = File::create(path)?;
//         let mut writer = BufWriter::new(file);
//
//         let mut iterator = self.rocksdb.raw_iterator();
//         iterator.seek_to_first();
//
//         while iterator.valid() {
//             if let (Some(key), Some(value)) = (iterator.key(), iterator.value()) {
//                 writer.write_all(&(key.len() as u32).to_le_bytes())?;
//                 writer.write_all(key)?;
//
//                 writer.write_all(&(value.len() as u32).to_le_bytes())?;
//                 writer.write_all(value)?;
//             }
//             iterator.next();
//         }
//
//         Ok(())
//     }
// }
