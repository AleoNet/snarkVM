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

use super::*;
use crate::store::helpers::{Map, MapRead};

use core::{fmt, fmt::Debug, hash::Hash};
use indexmap::IndexMap;
use std::{borrow::Cow, sync::atomic::Ordering};

#[derive(Clone)]
pub struct DataMap<K: Serialize + DeserializeOwned, V: Serialize + DeserializeOwned> {
    pub(super) database: RocksDB,
    pub(super) context: Vec<u8>,
    /// The part of the atomic batch belonging to the current map; it's typed for
    /// convenience and query performance, while the actual low-level atomic batch
    /// is untyped and stored in the database.
    pub(super) atomic_batch: Arc<Mutex<IndexMap<K, Option<V>>>>,
}

// This object is needed, as there currently is no way to "normally" iterate over
// rocksdb::WriteBatch, and the only way of doing so is via rocksdb::WriteBatchIterator,
// which needs to be implemented by some dedicated object.
struct CheckpointWriteBatch {
    // The partial/truncated write batch.
    batch: rocksdb::WriteBatch,
    // The number of items indicated by the checkpoint.
    limit: usize,
}

impl CheckpointWriteBatch {
    fn new(limit: usize) -> Self {
        Self { batch: Default::default(), limit }
    }
}

impl rocksdb::WriteBatchIterator for CheckpointWriteBatch {
    fn put(&mut self, key: Box<[u8]>, value: Box<[u8]>) {
        if self.batch.len() < self.limit {
            self.batch.put(key, value);
        }
    }

    fn delete(&mut self, key: Box<[u8]>) {
        if self.batch.len() < self.limit {
            self.batch.delete(key);
        }
    }
}

impl<
    'a,
    K: 'a + Copy + Clone + Debug + PartialEq + Eq + Hash + Serialize + DeserializeOwned + Send + Sync,
    V: 'a + Clone + PartialEq + Eq + Serialize + DeserializeOwned + Send + Sync,
> Map<'a, K, V> for DataMap<K, V>
{
    ///
    /// Inserts the given key-value pair into the map.
    ///
    fn insert(&self, key: K, value: V) -> Result<()> {
        // Prepare the prefixed key and serialized value.
        let raw_key = self.create_prefixed_key(&key)?;
        let raw_value = bincode::serialize(&value)?;

        match self.is_atomic_in_progress() {
            // If a batch is in progress, add the key-value pair to the batch.
            true => {
                self.atomic_batch.lock().insert(key, Some(value));
                self.database.atomic_batch.lock().put(raw_key, raw_value);
            }
            // Otherwise, insert the key-value pair directly into the map.
            false => {
                self.database.put(raw_key, raw_value)?;
            }
        }

        Ok(())
    }

    ///
    /// Removes the key-value pair for the given key from the map.
    ///
    fn remove(&self, key: &K) -> Result<()> {
        // Prepare the prefixed key.
        let raw_key = self.create_prefixed_key(key)?;

        match self.is_atomic_in_progress() {
            // If a batch is in progress, add the key to the batch.
            true => {
                self.atomic_batch.lock().insert(*key, None);
                self.database.atomic_batch.lock().delete(raw_key);
            }
            // Otherwise, remove the key-value pair directly from the map.
            false => {
                self.database.delete(raw_key)?;
            }
        }

        Ok(())
    }

    ///
    /// Begins an atomic operation. Any further calls to `insert` and `remove` will be queued
    /// without an actual write taking place until `finish_atomic` is called.
    ///
    fn start_atomic(&self) {
        // Increase the atomic batch depth.
        self.database.batch_depth.fetch_add(1, Ordering::SeqCst);
    }

    ///
    /// Schedules the writes already collected in the current atomic batch to be executed even
    /// if the atomic operation eventually gets aborted.
    ///
    fn atomic_checkpoint(&self) {
        let idx = self.database.atomic_batch.lock().len();
        self.database.checkpoint.store(idx, Ordering::SeqCst);
    }

    ///
    /// Checks whether an atomic operation is currently in progress. This can be done to ensure
    /// that lower-level operations don't start and finish their individual atomic write batch
    /// if they are already part of a larger one.
    ///
    fn is_atomic_in_progress(&self) -> bool {
        self.database.batch_depth.load(Ordering::SeqCst) != 0
    }

    ///
    /// Aborts the current atomic operation.
    ///
    fn abort_atomic(&self) {
        // Clear the typed atomic batch.
        self.atomic_batch.lock().clear();

        // Check if this is the final depth of the batch.
        // Subtraction happens separately from the check, as we don't want to perform it too
        // early in case this is the final depth and the batch still needs to be cleared first,
        // or partially executed in case there was a checkpoint.
        if self.database.batch_depth.load(Ordering::SeqCst) == 1 {
            // Retrieve the atomic batch.
            let batch = core::mem::take(&mut *self.database.atomic_batch.lock());

            // Retrieve the checkpoint index.
            let idx = self.database.checkpoint.swap(0, Ordering::SeqCst);

            if !batch.is_empty() && idx > 0 {
                // Truncate the batch to the last checkpoint.
                let mut partial_batch = CheckpointWriteBatch::new(idx);
                batch.iterate(&mut partial_batch);

                // Execute the operations from the partial batch atomically.
                if let Err(e) = self.database.rocksdb.write(partial_batch.batch) {
                    tracing::error!("Failed to execute an atomic batch up to a checkpoint: {e}");
                }
            }
        }

        // Subtract the batch depth.
        self.database.batch_depth.fetch_sub(1, Ordering::SeqCst);
    }

    ///
    /// Finishes an atomic operation, performing all the queued writes.
    ///
    fn finish_atomic(&self) -> Result<()> {
        // Clear the typed atomic batch.
        self.atomic_batch.lock().clear();

        // If the whole atomic operation is not unrolled yet, subtract the depth and return.
        // Subtraction happens separately from the check, as we don't want to perform it too
        // early in case this is the final depth and the batch still needs to be executed first.
        if self.database.batch_depth.load(Ordering::SeqCst) != 1 {
            self.database.batch_depth.fetch_sub(1, Ordering::SeqCst);
            return Ok(());
        }

        // Retrieve the atomic batch.
        let batch = core::mem::take(&mut *self.database.atomic_batch.lock());

        if !batch.is_empty() {
            // Execute all the operations atomically.
            self.database.rocksdb.write(batch)?;
        }

        // Subtract the batch depth (bringing it to 0).
        self.database.batch_depth.fetch_sub(1, Ordering::SeqCst);
        // Reset any atomic checkpoints we might have registered.
        self.database.checkpoint.store(0, Ordering::SeqCst);

        Ok(())
    }
}

impl<
    'a,
    K: 'a + Copy + Clone + Debug + PartialEq + Eq + Hash + Serialize + DeserializeOwned + Send + Sync,
    V: 'a + Clone + PartialEq + Eq + Serialize + DeserializeOwned + Send + Sync,
> MapRead<'a, K, V> for DataMap<K, V>
{
    type Iterator = Iter<'a, K, V>;
    type Keys = Keys<'a, K>;
    type PendingIterator =
        core::iter::Map<indexmap::map::IntoIter<K, Option<V>>, fn((K, Option<V>)) -> (Cow<'a, K>, Option<Cow<'a, V>>)>;
    type Values = Values<'a, V>;

    ///
    /// Returns `true` if the given key exists in the map.
    ///
    fn contains_key_confirmed<Q>(&self, key: &Q) -> Result<bool>
    where
        K: Borrow<Q>,
        Q: PartialEq + Eq + Hash + Serialize + ?Sized,
    {
        self.get_raw(key).map(|v| v.is_some())
    }

    ///
    /// Returns `true` if the given key exists in the map.
    /// This method first checks the atomic batch, and if it does not exist, then checks the map.
    ///
    fn contains_key_speculative<Q>(&self, key: &Q) -> Result<bool>
    where
        K: Borrow<Q>,
        Q: PartialEq + Eq + Hash + Serialize + ?Sized,
    {
        // If a batch is in progress, check the atomic batch first.
        if self.is_atomic_in_progress() {
            // If the key is present in the atomic batch, then check if the value is 'Some(V)'.
            if let Some(value) = self.atomic_batch.lock().get(key) {
                // If the value is 'Some(V)', then the key exists.
                // If the value is 'Some(None)', then the key is scheduled to be removed.
                return Ok(value.is_some());
            }
        }

        // Otherwise, check the map for the key.
        self.contains_key_confirmed(key)
    }

    ///
    /// Returns the value for the given key from the map, if it exists.
    ///
    fn get_confirmed<Q>(&'a self, key: &Q) -> Result<Option<Cow<'a, V>>>
    where
        K: Borrow<Q>,
        Q: PartialEq + Eq + Hash + Serialize + ?Sized,
    {
        match self.get_raw(key) {
            Ok(Some(bytes)) => Ok(Some(Cow::Owned(bincode::deserialize(&bytes)?))),
            Ok(None) => Ok(None),
            Err(e) => Err(e),
        }
    }

    ///
    /// Returns the current value for the given key if it is scheduled
    /// to be inserted as part of an atomic batch.
    ///
    /// If the key does not exist, returns `None`.
    /// If the key is removed in the batch, returns `Some(None)`.
    /// If the key is inserted in the batch, returns `Some(Some(value))`.
    ///
    fn get_pending<Q>(&self, key: &Q) -> Option<Option<V>>
    where
        K: Borrow<Q>,
        Q: PartialEq + Eq + Hash + Serialize + ?Sized,
    {
        if self.is_atomic_in_progress() { self.atomic_batch.lock().get(key).cloned() } else { None }
    }

    ///
    /// Returns an iterator visiting each key-value pair in the atomic batch.
    ///
    fn iter_pending(&'a self) -> Self::PendingIterator {
        self.atomic_batch.lock().clone().into_iter().map(|(k, v)| (Cow::Owned(k), v.map(|v| Cow::Owned(v))))
    }

    ///
    /// Returns an iterator visiting each key-value pair in the map.
    ///
    fn iter_confirmed(&'a self) -> Self::Iterator {
        Iter::new(self.database.prefix_iterator(&self.context))
    }

    ///
    /// Returns an iterator over each key in the map.
    ///
    fn keys_confirmed(&'a self) -> Self::Keys {
        Keys::new(self.database.prefix_iterator(&self.context))
    }

    ///
    /// Returns an iterator over each value in the map.
    ///
    fn values_confirmed(&'a self) -> Self::Values {
        Values::new(self.database.prefix_iterator(&self.context))
    }
}

impl<K: Serialize + DeserializeOwned, V: Serialize + DeserializeOwned> DataMap<K, V> {
    #[inline]
    fn create_prefixed_key<Q>(&self, key: &Q) -> Result<Vec<u8>>
    where
        K: Borrow<Q>,
        Q: Serialize + ?Sized,
    {
        let mut raw_key = self.context.clone();
        bincode::serialize_into(&mut raw_key, &key)?;
        Ok(raw_key)
    }

    fn get_raw<Q>(&self, key: &Q) -> Result<Option<rocksdb::DBPinnableSlice>>
    where
        K: Borrow<Q>,
        Q: Serialize + ?Sized,
    {
        let raw_key = self.create_prefixed_key(key)?;
        match self.database.get_pinned(&raw_key)? {
            Some(data) => Ok(Some(data)),
            None => Ok(None),
        }
    }
}

impl<K: Serialize + DeserializeOwned, V: Serialize + DeserializeOwned> fmt::Debug for DataMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DataMap").field("context", &self.context).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::helpers::rocksdb::{internal::tests::temp_dir, MapID, TestMap};
    use console::{account::Address, network::Testnet3, prelude::FromStr};

    use anyhow::bail;
    use serial_test::serial;
    use tracing_test::traced_test;

    type CurrentNetwork = Testnet3;

    // Below are a few objects that mimic the way our DataMaps are organized,
    // in order to provide a more accurate test setup for some scenarios.

    fn open_map_testing_from_db<K: Serialize + DeserializeOwned, V: Serialize + DeserializeOwned, T: Into<u16>>(
        database: RocksDB,
        map_id: T,
    ) -> DataMap<K, V> {
        // Combine contexts to create a new scope.
        let mut context = database.network_id.to_le_bytes().to_vec();
        context.extend_from_slice(&(map_id.into()).to_le_bytes());

        // Return the DataMap.
        DataMap { database, context, atomic_batch: Default::default() }
    }

    struct TestStorage {
        own_map: DataMap<usize, String>,
        extra_maps: TestStorage2,
    }

    impl TestStorage {
        fn open() -> Self {
            // Initialize a database.
            let database = RocksDB::open_testing(temp_dir(), None).expect("Failed to open a test database");

            Self {
                own_map: open_map_testing_from_db(database.clone(), MapID::Test(TestMap::Test)),
                extra_maps: TestStorage2::open(database),
            }
        }

        fn start_atomic(&self) {
            self.own_map.start_atomic();
            self.extra_maps.start_atomic();
        }

        fn is_atomic_in_progress(&self) -> bool {
            self.own_map.is_atomic_in_progress() || self.extra_maps.is_atomic_in_progress()
        }

        fn abort_atomic(&self) {
            self.own_map.abort_atomic();
            self.extra_maps.abort_atomic();
        }

        fn finish_atomic(&self) -> Result<()> {
            self.own_map.finish_atomic()?;
            self.extra_maps.finish_atomic()
        }

        // While the methods above mimic the typical snarkVM ones, this method is purely for testing.
        fn is_atomic_in_progress_everywhere(&self) -> bool {
            self.own_map.is_atomic_in_progress()
                && self.extra_maps.own_map1.is_atomic_in_progress()
                && self.extra_maps.own_map1.is_atomic_in_progress()
                && self.extra_maps.extra_maps.own_map.is_atomic_in_progress()
        }
    }

    struct TestStorage2 {
        own_map1: DataMap<usize, String>,
        own_map2: DataMap<usize, String>,
        extra_maps: TestStorage3,
    }

    impl TestStorage2 {
        fn open(database: RocksDB) -> Self {
            Self {
                own_map1: open_map_testing_from_db(database.clone(), MapID::Test(TestMap::Test2)),
                own_map2: open_map_testing_from_db(database.clone(), MapID::Test(TestMap::Test3)),
                extra_maps: TestStorage3::open(database),
            }
        }

        fn start_atomic(&self) {
            self.own_map1.start_atomic();
            self.own_map2.start_atomic();
            self.extra_maps.start_atomic();
        }

        fn is_atomic_in_progress(&self) -> bool {
            self.own_map1.is_atomic_in_progress()
                || self.own_map2.is_atomic_in_progress()
                || self.extra_maps.is_atomic_in_progress()
        }

        fn abort_atomic(&self) {
            self.own_map1.abort_atomic();
            self.own_map2.abort_atomic();
            self.extra_maps.abort_atomic();
        }

        fn finish_atomic(&self) -> Result<()> {
            self.own_map1.finish_atomic()?;
            self.own_map2.finish_atomic()?;
            self.extra_maps.finish_atomic()
        }
    }

    struct TestStorage3 {
        own_map: DataMap<usize, String>,
    }

    impl TestStorage3 {
        fn open(database: RocksDB) -> Self {
            Self { own_map: open_map_testing_from_db(database, MapID::Test(TestMap::Test4)) }
        }

        fn start_atomic(&self) {
            self.own_map.start_atomic();
        }

        fn is_atomic_in_progress(&self) -> bool {
            self.own_map.is_atomic_in_progress()
        }

        fn abort_atomic(&self) {
            self.own_map.abort_atomic();
        }

        fn finish_atomic(&self) -> Result<()> {
            self.own_map.finish_atomic()
        }
    }

    #[test]
    #[serial]
    fn test_contains_key() {
        // Initialize an address.
        let address =
            Address::<CurrentNetwork>::from_str("aleo1q6qstg8q8shwqf5m6q5fcenuwsdqsvp4hhsgfnx5chzjm3secyzqt9mxm8")
                .unwrap();

        // Initialize a map.
        let map: DataMap<Address<CurrentNetwork>, ()> =
            RocksDB::open_map_testing(temp_dir(), None, MapID::Test(TestMap::Test)).expect("Failed to open data map");
        map.insert(address, ()).expect("Failed to insert into data map");
        assert!(map.contains_key_confirmed(&address).unwrap());
    }

    #[test]
    #[serial]
    #[traced_test]
    fn test_insert_and_get_speculative() {
        // Initialize a map.
        let map: DataMap<usize, String> =
            RocksDB::open_map_testing(temp_dir(), None, MapID::Test(TestMap::Test)).expect("Failed to open data map");

        // Sanity check.
        assert!(map.iter_confirmed().next().is_none());

        /* test atomic insertions */

        // Start an atomic write batch.
        map.start_atomic();

        // Insert an item into the map.
        map.insert(0, "0".to_string()).unwrap();

        // Check that the item is not yet in the map.
        assert!(map.get_confirmed(&0).unwrap().is_none());
        // Check that the item is in the batch.
        assert_eq!(map.get_pending(&0), Some(Some("0".to_string())));
        // Check that the item can be speculatively retrieved.
        assert_eq!(map.get_speculative(&0).unwrap(), Some(Cow::Owned("0".to_string())));

        // Queue (since a batch is in progress) NUM_ITEMS insertions.
        for i in 1..10 {
            // Update the item in the map.
            map.insert(0, i.to_string()).unwrap();

            // Check that the item is not yet in the map.
            assert!(map.get_confirmed(&0).unwrap().is_none());
            // Check that the updated item is in the batch.
            assert_eq!(map.get_pending(&0), Some(Some(i.to_string())));
            // Check that the updated item can be speculatively retrieved.
            assert_eq!(map.get_speculative(&0).unwrap(), Some(Cow::Owned(i.to_string())));
        }

        // The map should still contain no items.
        assert!(map.iter_confirmed().next().is_none());

        // Finish the current atomic write batch.
        map.finish_atomic().unwrap();

        // Check that the item is present in the map now.
        assert_eq!(map.get_confirmed(&0).unwrap(), Some(Cow::Owned("9".to_string())));
        // Check that the item is not in the batch.
        assert_eq!(map.get_pending(&0), None);
        // Check that the item can be speculatively retrieved.
        assert_eq!(map.get_speculative(&0).unwrap(), Some(Cow::Owned("9".to_string())));
    }

    #[test]
    #[serial]
    #[traced_test]
    fn test_remove_and_get_speculative() {
        // Initialize a map.
        let map: DataMap<usize, String> =
            RocksDB::open_map_testing(temp_dir(), None, MapID::Test(TestMap::Test)).expect("Failed to open data map");

        // Sanity check.
        assert!(map.iter_confirmed().next().is_none());

        // Insert an item into the map.
        map.insert(0, "0".to_string()).unwrap();

        // Check that the item is present in the map .
        assert_eq!(map.get_confirmed(&0).unwrap(), Some(Cow::Owned("0".to_string())));
        // Check that the item is not in the batch.
        assert_eq!(map.get_pending(&0), None);
        // Check that the item can be speculatively retrieved.
        assert_eq!(map.get_speculative(&0).unwrap(), Some(Cow::Owned("0".to_string())));

        /* test atomic removals */

        // Start an atomic write batch.
        map.start_atomic();

        // Remove the item from the map.
        map.remove(&0).unwrap();

        // Check that the item still exists in the map.
        assert_eq!(map.get_confirmed(&0).unwrap(), Some(Cow::Owned("0".to_string())));
        // Check that the item is removed in the batch.
        assert_eq!(map.get_pending(&0), Some(None));
        // Check that the item is removed when speculatively retrieved.
        assert_eq!(map.get_speculative(&0).unwrap(), None);

        // Try removing the item again.
        map.remove(&0).unwrap();

        // Check that the item still exists in the map.
        assert_eq!(map.get_confirmed(&0).unwrap(), Some(Cow::Owned("0".to_string())));
        // Check that the item is removed in the batch.
        assert_eq!(map.get_pending(&0), Some(None));
        // Check that the item is removed when speculatively retrieved.
        assert_eq!(map.get_speculative(&0).unwrap(), None);

        // Finish the current atomic write batch.
        map.finish_atomic().unwrap();

        // Check that the item is not present in the map now.
        assert!(map.get_confirmed(&0).unwrap().is_none());
        // Check that the item is not in the batch.
        assert_eq!(map.get_pending(&0), None);
        // Check that the item is removed when speculatively retrieved.
        assert_eq!(map.get_speculative(&0).unwrap(), None);

        // Check that the map is empty now.
        assert!(map.iter_confirmed().next().is_none());
    }

    #[test]
    #[serial]
    #[traced_test]
    fn test_atomic_writes_are_batched() {
        // The number of items that will be inserted into the map.
        const NUM_ITEMS: usize = 10;

        // Initialize a map.
        let map: DataMap<usize, String> =
            RocksDB::open_map_testing(temp_dir(), None, MapID::Test(TestMap::Test)).expect("Failed to open data map");

        // Sanity check.
        assert!(map.iter_confirmed().next().is_none());

        /* test atomic insertions */

        // Start an atomic write batch.
        map.start_atomic();

        // Queue (since a batch is in progress) NUM_ITEMS insertions.
        for i in 0..NUM_ITEMS {
            map.insert(i, i.to_string()).unwrap();
            // Ensure that the item is queued for insertion.
            assert_eq!(map.get_pending(&i), Some(Some(i.to_string())));
            // Ensure that the item can be found with a speculative get.
            assert_eq!(map.get_speculative(&i).unwrap(), Some(Cow::Owned(i.to_string())));
        }

        // The map should still contain no items.
        assert!(map.iter_confirmed().next().is_none());

        // Finish the current atomic write batch.
        map.finish_atomic().unwrap();

        // Check that the items are present in the map now.
        for i in 0..NUM_ITEMS {
            assert_eq!(map.get_confirmed(&i).unwrap(), Some(Cow::Borrowed(&i.to_string())));
        }

        /* test atomic removals */

        // Start an atomic write batch.
        map.start_atomic();

        // Queue (since a batch is in progress) NUM_ITEMS removals.
        for i in 0..NUM_ITEMS {
            map.remove(&i).unwrap();
            // Ensure that the item is NOT queued for insertion.
            assert_eq!(map.get_pending(&i), Some(None));
        }

        // The map should still contains all the items.
        assert_eq!(map.iter_confirmed().count(), NUM_ITEMS);

        // Finish the current atomic write batch.
        map.finish_atomic().unwrap();

        // Check that the map is empty now.
        assert!(map.iter_confirmed().next().is_none());
    }

    #[test]
    #[serial]
    #[traced_test]
    fn test_atomic_writes_can_be_aborted() {
        // The number of items that will be queued to be inserted into the map.
        const NUM_ITEMS: usize = 10;

        // Initialize a map.
        let map: DataMap<usize, String> =
            RocksDB::open_map_testing(temp_dir(), None, MapID::Test(TestMap::Test)).expect("Failed to open data map");

        // Sanity check.
        assert!(map.iter_confirmed().next().is_none());

        // Start an atomic write batch.
        map.start_atomic();

        // Queue (since a batch is in progress) NUM_ITEMS insertions.
        for i in 0..NUM_ITEMS {
            map.insert(i, i.to_string()).unwrap();
        }

        // The map should still contain no items.
        assert!(map.iter_confirmed().next().is_none());

        // Abort the current atomic write batch.
        map.abort_atomic();

        // The map should still contain no items.
        assert!(map.iter_confirmed().next().is_none());

        // Start another atomic write batch.
        map.start_atomic();

        // Queue (since a batch is in progress) NUM_ITEMS insertions.
        for i in 0..NUM_ITEMS {
            map.insert(i, i.to_string()).unwrap();
        }

        // Finish the current atomic write batch.
        map.finish_atomic().unwrap();

        // The map should contain NUM_ITEMS items now.
        assert_eq!(map.iter_confirmed().count(), NUM_ITEMS);
    }

    #[test]
    #[serial]
    #[traced_test]
    fn test_abort_with_checkpoint() {
        // The number of items that will be queued to be inserted into the map.
        const NUM_ITEMS: usize = 10;

        // Initialize a map.
        let map: DataMap<usize, String> =
            RocksDB::open_map_testing(temp_dir(), None, MapID::Test(TestMap::Test)).expect("Failed to open data map");

        // Sanity check.
        assert!(map.iter_confirmed().next().is_none());

        // Start an atomic write batch.
        map.start_atomic();

        // Queue (since a batch is in progress) NUM_ITEMS / 2 insertions.
        for i in 0..NUM_ITEMS / 2 {
            map.insert(i, i.to_string()).unwrap();
        }

        // Perform a checkpoint.
        map.atomic_checkpoint();

        // Queue (since a batch is in progress) the other NUM_ITEMS / 2 insertions.
        for i in (NUM_ITEMS / 2)..NUM_ITEMS {
            map.insert(i, i.to_string()).unwrap();
        }

        // Abort the current atomic write batch.
        map.abort_atomic();

        // The map should contain NUM_ITEMS / 2.
        assert_eq!(map.iter_confirmed().count(), NUM_ITEMS / 2);

        // Make sure the checkpoint index is cleared.
        assert_eq!(map.database.checkpoint.load(Ordering::SeqCst), 0);

        // Make sure the pending batch is empty.
        assert!(map.database.atomic_batch.lock().is_empty());
    }

    #[test]
    #[serial]
    #[traced_test]
    fn test_nested_atomic_write_batch_success() -> Result<()> {
        // Initialize a multi-layer test storage.
        let test_storage = TestStorage::open();

        // Sanity check.
        assert!(test_storage.own_map.iter_confirmed().next().is_none());
        assert!(test_storage.extra_maps.own_map1.iter_confirmed().next().is_none());
        assert!(test_storage.extra_maps.own_map2.iter_confirmed().next().is_none());
        assert!(test_storage.extra_maps.extra_maps.own_map.iter_confirmed().next().is_none());

        // Note: all the checks going through .database can be performed on any one
        // of the objects, as all of them share the same instance of the database.

        // Ensure the batch depth is 0, meaning the atomic operation has not started yet.
        assert_eq!(0, test_storage.own_map.database.batch_depth.load(Ordering::SeqCst));
        assert!(!test_storage.is_atomic_in_progress_everywhere());

        // Start an atomic write batch.
        crate::atomic_write_batch!(test_storage, {
            // Ensure the batch depth is 4, as all of the underlying maps have called start_atomic.
            assert_eq!(4, test_storage.own_map.database.batch_depth.load(Ordering::SeqCst));
            assert!(test_storage.is_atomic_in_progress_everywhere());

            // Write an item into the first map.
            test_storage.own_map.insert(0, 0.to_string()).unwrap();

            // Start another atomic write batch.
            crate::atomic_write_batch!(test_storage.extra_maps.own_map1, {
                // Ensure the batch depth is still 4, as only the first, outermost call triggers this increase.
                assert_eq!(4, test_storage.extra_maps.own_map1.database.batch_depth.load(Ordering::SeqCst));
                assert!(test_storage.is_atomic_in_progress_everywhere());

                // Write an item into the second map.
                test_storage.extra_maps.own_map1.insert(1, 1.to_string()).unwrap();

                // Write an item into the third map.
                test_storage.extra_maps.own_map2.insert(2, 2.to_string()).unwrap();

                // Start another atomic write batch.
                crate::atomic_write_batch!(test_storage.extra_maps.extra_maps.own_map, {
                    // Ensure the batch depth is still 4.
                    assert_eq!(
                        4,
                        test_storage.extra_maps.extra_maps.own_map.database.batch_depth.load(Ordering::SeqCst)
                    );
                    assert!(test_storage.extra_maps.extra_maps.own_map.is_atomic_in_progress());

                    // Write an item into the fourth map.
                    test_storage.extra_maps.extra_maps.own_map.insert(3, 3.to_string()).unwrap();

                    Ok(())
                });

                // Ensure the batch depth is still 4, as only the last, outermost call triggers the decrease.
                assert_eq!(4, test_storage.own_map.database.batch_depth.load(Ordering::SeqCst));
                assert!(test_storage.is_atomic_in_progress_everywhere());

                Ok(())
            });

            // Ensure the batch depth is still 4.
            assert_eq!(4, test_storage.own_map.database.batch_depth.load(Ordering::SeqCst));
            assert!(test_storage.is_atomic_in_progress_everywhere());

            Ok(())
        });

        // Ensure the batch depth is 0 now, meaning the atomic operation has concluded.
        assert_eq!(0, test_storage.own_map.database.batch_depth.load(Ordering::SeqCst));
        assert!(!test_storage.is_atomic_in_progress_everywhere());

        // Ensure that all the items are present.
        assert_eq!(test_storage.own_map.iter_confirmed().count(), 1);
        assert_eq!(test_storage.extra_maps.own_map1.iter_confirmed().count(), 1);
        assert_eq!(test_storage.extra_maps.own_map2.iter_confirmed().count(), 1);
        assert_eq!(test_storage.extra_maps.extra_maps.own_map.iter_confirmed().count(), 1);

        // The atomic_write_batch macro uses ?, so the test returns a Result for simplicity.
        Ok(())
    }

    #[test]
    #[serial]
    #[traced_test]
    fn test_nested_atomic_write_batch_abort() {
        // We'll want to execute the atomic write batch in its own function, in order to be able to
        // inspect the aftermatch after an error, as opposed to returning from the whole test.
        fn execute_atomic_write_batch(test_storage: &TestStorage) -> Result<()> {
            // Start an atomic write batch.
            crate::atomic_write_batch!(test_storage, {
                // Ensure the batch depth is 4, as all of the underlying maps have called start_atomic.
                assert_eq!(4, test_storage.own_map.database.batch_depth.load(Ordering::SeqCst));
                assert!(test_storage.is_atomic_in_progress_everywhere());

                // Write an item into the first map.
                test_storage.own_map.insert(0, 0.to_string()).unwrap();

                // Start another atomic write batch.
                crate::atomic_write_batch!(test_storage.extra_maps.own_map1, {
                    // Ensure the batch depth is still 4, as only the first, outermost call triggers this increase.
                    assert_eq!(4, test_storage.extra_maps.own_map1.database.batch_depth.load(Ordering::SeqCst));
                    assert!(test_storage.is_atomic_in_progress_everywhere());

                    // Write an item into the second map.
                    test_storage.extra_maps.own_map1.insert(1, 1.to_string()).unwrap();

                    // Perform an atomic checkpoint.
                    test_storage.extra_maps.own_map1.atomic_checkpoint();

                    // Write an item into the third map.
                    test_storage.extra_maps.own_map2.insert(2, 2.to_string()).unwrap();

                    // Start another atomic write batch.
                    crate::atomic_write_batch!(test_storage.extra_maps.extra_maps.own_map, {
                        // Ensure the batch depth is still 4.
                        assert_eq!(
                            4,
                            test_storage.extra_maps.extra_maps.own_map.database.batch_depth.load(Ordering::SeqCst)
                        );
                        assert!(test_storage.is_atomic_in_progress_everywhere());

                        // Write an item into the fourth map.
                        test_storage.extra_maps.extra_maps.own_map.insert(3, 3.to_string()).unwrap();

                        // Abort the atomic batch via a simulated error.
                        bail!("An error that will trigger a cascade abort.");
                    });

                    // Ensure the batch depth is still 4, as only the last, outermost call triggers the decrease.
                    assert_eq!(4, test_storage.own_map.database.batch_depth.load(Ordering::SeqCst));
                    assert!(test_storage.is_atomic_in_progress_everywhere());

                    Ok(())
                });

                // Ensure the batch depth is still 4.
                assert_eq!(4, test_storage.own_map.database.batch_depth.load(Ordering::SeqCst));
                assert!(test_storage.is_atomic_in_progress_everywhere());

                Ok(())
            });

            Ok(())
        }

        // Initialize a multi-layer test storage.
        let test_storage = TestStorage::open();

        // Sanity check.
        assert!(test_storage.own_map.iter_confirmed().next().is_none());
        assert!(test_storage.extra_maps.own_map1.iter_confirmed().next().is_none());
        assert!(test_storage.extra_maps.own_map2.iter_confirmed().next().is_none());
        assert!(test_storage.extra_maps.extra_maps.own_map.iter_confirmed().next().is_none());

        // Note: all the checks going through .database can be performed on any one
        // of the objects, as all of them share the same instance of the database.

        // Ensure the batch depth is 0.
        assert_eq!(0, test_storage.own_map.database.batch_depth.load(Ordering::SeqCst));
        assert!(!test_storage.is_atomic_in_progress_everywhere());

        // Perform the atomic operations defined in the free function at the beginning of the test.
        assert!(execute_atomic_write_batch(&test_storage).is_err());

        // Ensure the batch depth is 0 now.
        assert_eq!(0, test_storage.own_map.database.batch_depth.load(Ordering::SeqCst));
        assert!(!test_storage.is_atomic_in_progress_everywhere());

        // Ensure that all the items up until the checkpoint are present.
        assert_eq!(test_storage.own_map.iter_confirmed().count(), 1);
        assert_eq!(test_storage.extra_maps.own_map1.iter_confirmed().count(), 1);

        // Ensure that all the items after the checkpoint are not present.
        assert_eq!(test_storage.extra_maps.own_map2.iter_confirmed().count(), 0);
        assert_eq!(test_storage.extra_maps.extra_maps.own_map.iter_confirmed().count(), 0);
    }
}
