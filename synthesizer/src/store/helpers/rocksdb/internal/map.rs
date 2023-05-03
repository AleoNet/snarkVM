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
        // Determine if an atomic batch is in progress.
        let is_batch = self.is_atomic_in_progress();

        // Prepare the prefixed key and serialized value.
        let raw_key = self.create_prefixed_key(&key)?;
        let raw_value = bincode::serialize(&value)?;

        match is_batch {
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
        // Determine if an atomic batch is in progress.
        let is_batch = self.is_atomic_in_progress();

        // Prepare the prefixed key.
        let raw_key = self.create_prefixed_key(key)?;

        match is_batch {
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

    use serial_test::serial;
    use tracing_test::traced_test;

    type CurrentNetwork = Testnet3;

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
        for i in 0..NUM_ITEMS / 2 {
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
    fn test_nested_atomic_write_batch() -> Result<()> {
        // Initialize a map.
        let map: DataMap<usize, String> =
            RocksDB::open_map_testing(temp_dir(), None, MapID::Test(TestMap::Test)).expect("Failed to open data map");

        // Sanity check.
        assert!(map.iter_confirmed().next().is_none());

        // Ensure the batch depth is 0.
        assert_eq!(0, map.database.batch_depth.load(Ordering::SeqCst));

        // Start an atomic write batch.
        crate::atomic_write_batch!(map, {

            // Ensure the batch depth is 1.
            assert_eq!(1, map.database.batch_depth.load(Ordering::SeqCst));

            // Write the first item.
            map.insert(0, 0.to_string()).unwrap();

            // Start another atomic write batch.
            crate::atomic_write_batch!(map, {

                // Ensure the batch depth is 2.
                assert_eq!(2, map.database.batch_depth.load(Ordering::SeqCst));

                // Write the second item.
                map.insert(1, 1.to_string()).unwrap();

                Ok(())
            });

            // Ensure the batch depth is 1.
            assert_eq!(1, map.database.batch_depth.load(Ordering::SeqCst));

            Ok(())
        });

        // Ensure the batch depth is 0.
        assert_eq!(0, map.database.batch_depth.load(Ordering::SeqCst));

        Ok(())
    }
}
