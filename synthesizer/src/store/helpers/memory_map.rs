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

use crate::store::helpers::{Map, MapRead};
use console::network::prelude::*;
use indexmap::IndexMap;

use core::{borrow::Borrow, hash::Hash};
use indexmap::map;
use parking_lot::{Mutex, RwLock};
use std::{
    borrow::Cow,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
};

#[derive(Clone)]
pub struct MemoryMap<
    K: Copy + Clone + PartialEq + Eq + Hash + Serialize + for<'de> Deserialize<'de> + Send + Sync,
    V: Clone + PartialEq + Eq + Serialize + for<'de> Deserialize<'de> + Send + Sync,
> {
    map: Arc<RwLock<IndexMap<K, V>>>,
    batch_in_progress: Arc<AtomicBool>,
    atomic_batch: Arc<Mutex<IndexMap<K, Option<V>>>>,
}

impl<
    K: Copy + Clone + PartialEq + Eq + Hash + Serialize + for<'de> Deserialize<'de> + Send + Sync,
    V: Clone + PartialEq + Eq + Serialize + for<'de> Deserialize<'de> + Send + Sync,
> Default for MemoryMap<K, V>
{
    fn default() -> Self {
        Self { map: Default::default(), batch_in_progress: Default::default(), atomic_batch: Default::default() }
    }
}

impl<
    K: Copy + Clone + PartialEq + Eq + Hash + Serialize + for<'de> Deserialize<'de> + Send + Sync,
    V: Clone + PartialEq + Eq + Serialize + for<'de> Deserialize<'de> + Send + Sync,
> FromIterator<(K, V)> for MemoryMap<K, V>
{
    /// Initializes a new `MemoryMap` from the given iterator.
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        Self {
            map: Arc::new(RwLock::new(IndexMap::from_iter(iter))),
            batch_in_progress: Default::default(),
            atomic_batch: Default::default(),
        }
    }
}

impl<
    'a,
    K: 'a + Copy + Clone + PartialEq + Eq + Hash + Serialize + for<'de> Deserialize<'de> + Send + Sync,
    V: 'a + Clone + PartialEq + Eq + Serialize + for<'de> Deserialize<'de> + Send + Sync,
> Map<'a, K, V> for MemoryMap<K, V>
{
    ///
    /// Inserts the given key-value pair into the map.
    ///
    fn insert(&self, key: K, value: V) -> Result<()> {
        // Determine if an atomic batch is in progress.
        let is_batch = self.batch_in_progress.load(Ordering::SeqCst);

        match is_batch {
            // If a batch is in progress, add the key-value pair to the batch.
            true => {
                self.atomic_batch.lock().insert(key, Some(value));
            }
            // Otherwise, insert the key-value pair directly into the map.
            false => {
                self.map.write().insert(key, value);
            }
        }
        Ok(())
    }

    ///
    /// Removes the key-value pair for the given key from the map.
    ///
    fn remove(&self, key: &K) -> Result<()> {
        // Determine if an atomic batch is in progress.
        let is_batch = self.batch_in_progress.load(Ordering::SeqCst);

        match is_batch {
            // If a batch is in progress, add the key-None pair to the batch.
            true => {
                self.atomic_batch.lock().insert(*key, None);
            }
            // Otherwise, remove the key-value pair directly from the map.
            false => {
                self.map.write().shift_remove(key);
            }
        }
        Ok(())
    }

    ///
    /// Begins an atomic operation. Any further calls to `insert` and `remove` will be queued
    /// without an actual write taking place until `finish_atomic` is called.
    ///
    fn start_atomic(&self) {
        // Set the atomic batch flag to `true`.
        self.batch_in_progress.store(true, Ordering::SeqCst);
        // Ensure that the atomic batch is empty.
        assert!(self.atomic_batch.lock().is_empty());
    }

    ///
    /// Checks whether an atomic operation is currently in progress. This can be done to ensure
    /// that lower-level operations don't start and finish their individual atomic write batch
    /// if they are already part of a larger one.
    ///
    fn is_atomic_in_progress(&self) -> bool {
        self.batch_in_progress.load(Ordering::SeqCst)
    }

    ///
    /// Aborts the current atomic operation.
    ///
    fn abort_atomic(&self) {
        // Clear the atomic batch.
        *self.atomic_batch.lock() = Default::default();
        // Set the atomic batch flag to `false`.
        self.batch_in_progress.store(false, Ordering::SeqCst);
    }

    ///
    /// Finishes an atomic operation, performing all the queued writes.
    ///
    fn finish_atomic(&self) -> Result<()> {
        // Retrieve the atomic batch.
        let operations = core::mem::take(&mut *self.atomic_batch.lock());

        if !operations.is_empty() {
            // Acquire a write lock on the map.
            let mut locked_map = self.map.write();
            // Perform all the queued operations.
            for operation in operations {
                match operation {
                    (key, Some(value)) => locked_map.insert(key, value),
                    (key, None) => locked_map.remove(&key),
                };
            }
        }

        // Set the atomic batch flag to `false`.
        self.batch_in_progress.store(false, Ordering::SeqCst);

        Ok(())
    }
}

impl<
    'a,
    K: 'a + Copy + Clone + PartialEq + Eq + Hash + Serialize + for<'de> Deserialize<'de> + Send + Sync,
    V: 'a + Clone + PartialEq + Eq + Serialize + for<'de> Deserialize<'de> + Send + Sync,
> MapRead<'a, K, V> for MemoryMap<K, V>
{
    type Iterator = core::iter::Map<map::IntoIter<K, V>, fn((K, V)) -> (Cow<'a, K>, Cow<'a, V>)>;
    type Keys = core::iter::Map<map::IntoKeys<K, V>, fn(K) -> Cow<'a, K>>;
    type Values = core::iter::Map<map::IntoValues<K, V>, fn(V) -> Cow<'a, V>>;

    ///
    /// Returns `true` if the given key exists in the map.
    ///
    fn contains_key<Q>(&self, key: &Q) -> Result<bool>
    where
        K: Borrow<Q>,
        Q: PartialEq + Eq + Hash + Serialize + ?Sized,
    {
        Ok(self.map.read().contains_key(key))
    }

    ///
    /// Returns the value for the given key from the map, if it exists.
    ///
    fn get<Q>(&'a self, key: &Q) -> Result<Option<Cow<'a, V>>>
    where
        K: Borrow<Q>,
        Q: PartialEq + Eq + Hash + Serialize + ?Sized,
    {
        Ok(self.map.read().get(key).cloned().map(Cow::Owned))
    }

    ///
    /// Returns the current value for the given key if it is scheduled
    /// to be inserted as part of an atomic batch.
    ///
    /// If the key does not exist, returns `None`.
    /// If the key is removed in the batch, returns `Some(None)`.
    /// If the key is inserted in the batch, returns `Some(Some(value))`.
    ///
    fn get_batched<Q>(&self, key: &Q) -> Option<Option<V>>
    where
        K: Borrow<Q>,
        Q: PartialEq + Eq + Hash + Serialize + ?Sized,
    {
        // Return early if there is no atomic batch in progress.
        if self.batch_in_progress.load(Ordering::SeqCst) { self.atomic_batch.lock().get(key).cloned() } else { None }
    }

    ///
    /// Returns an iterator visiting each key-value pair in the map.
    ///
    fn iter(&'a self) -> Self::Iterator {
        self.map.read().clone().into_iter().map(|(k, v)| (Cow::Owned(k), Cow::Owned(v)))
    }

    ///
    /// Returns an iterator over each key in the map.
    ///
    fn keys(&'a self) -> Self::Keys {
        self.map.read().clone().into_keys().map(Cow::Owned)
    }

    ///
    /// Returns an iterator over each value in the map.
    ///
    fn values(&'a self) -> Self::Values {
        self.map.read().clone().into_values().map(Cow::Owned)
    }
}

impl<
    K: Copy + Clone + PartialEq + Eq + Hash + Serialize + for<'de> Deserialize<'de> + Send + Sync,
    V: Clone + PartialEq + Eq + Serialize + for<'de> Deserialize<'de> + Send + Sync,
> Deref for MemoryMap<K, V>
{
    type Target = Arc<RwLock<IndexMap<K, V>>>;

    fn deref(&self) -> &Self::Target {
        &self.map
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::{account::Address, network::Testnet3};

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_contains_key() {
        // Initialize an address.
        let address =
            Address::<CurrentNetwork>::from_str("aleo1q6qstg8q8shwqf5m6q5fcenuwsdqsvp4hhsgfnx5chzjm3secyzqt9mxm8")
                .unwrap();

        // Sanity check.
        let addresses: IndexMap<Address<CurrentNetwork>, ()> = [(address, ())].into_iter().collect();
        assert!(addresses.contains_key(&address));

        // Initialize a map.
        let map: MemoryMap<Address<CurrentNetwork>, ()> = [(address, ())].into_iter().collect();
        assert!(map.contains_key(&address).unwrap());
    }

    #[test]
    fn test_insert_and_get_speculative() {
        // Initialize a map.
        let map: MemoryMap<usize, String> = Default::default();

        // Sanity check.
        assert!(map.iter().next().is_none());

        /* test atomic insertions */

        // Start an atomic write batch.
        map.start_atomic();

        // Insert an item into the map.
        map.insert(0, "0".to_string()).unwrap();

        // Check that the item is not yet in the map.
        assert!(map.get(&0).unwrap().is_none());
        // Check that the item is in the batch.
        assert_eq!(map.get_batched(&0), Some(Some("0".to_string())));
        // Check that the item can be speculatively retrieved.
        assert_eq!(map.get_speculative(&0).unwrap(), Some(Cow::Owned("0".to_string())));

        // Queue (since a batch is in progress) NUM_ITEMS insertions.
        for i in 1..10 {
            // Update the item in the map.
            map.insert(0, i.to_string()).unwrap();

            // Check that the item is not yet in the map.
            assert!(map.get(&0).unwrap().is_none());
            // Check that the updated item is in the batch.
            assert_eq!(map.get_batched(&0), Some(Some(i.to_string())));
            // Check that the updated item can be speculatively retrieved.
            assert_eq!(map.get_speculative(&0).unwrap(), Some(Cow::Owned(i.to_string())));
        }

        // The map should still contain no items.
        assert!(map.iter().next().is_none());

        // Finish the current atomic write batch.
        map.finish_atomic().unwrap();

        // Check that the item is present in the map now.
        assert_eq!(map.get(&0).unwrap(), Some(Cow::Owned("9".to_string())));
        // Check that the item is not in the batch.
        assert_eq!(map.get_batched(&0), None);
        // Check that the item can be speculatively retrieved.
        assert_eq!(map.get_speculative(&0).unwrap(), Some(Cow::Owned("9".to_string())));
    }

    #[test]
    fn test_remove_and_get_speculative() {
        // Initialize a map.
        let map: MemoryMap<usize, String> = Default::default();

        // Sanity check.
        assert!(map.iter().next().is_none());

        // Insert an item into the map.
        map.insert(0, "0".to_string()).unwrap();

        // Check that the item is present in the map .
        assert_eq!(map.get(&0).unwrap(), Some(Cow::Owned("0".to_string())));
        // Check that the item is not in the batch.
        assert_eq!(map.get_batched(&0), None);
        // Check that the item can be speculatively retrieved.
        assert_eq!(map.get_speculative(&0).unwrap(), Some(Cow::Owned("0".to_string())));

        /* test atomic removals */

        // Start an atomic write batch.
        map.start_atomic();

        // Remove the item from the map.
        map.remove(&0).unwrap();

        // Check that the item still exists in the map.
        assert_eq!(map.get(&0).unwrap(), Some(Cow::Owned("0".to_string())));
        // Check that the item is removed in the batch.
        assert_eq!(map.get_batched(&0), Some(None));
        // Check that the item is removed when speculatively retrieved.
        assert_eq!(map.get_speculative(&0).unwrap(), None);

        // Try removing the item again.
        map.remove(&0).unwrap();

        // Check that the item still exists in the map.
        assert_eq!(map.get(&0).unwrap(), Some(Cow::Owned("0".to_string())));
        // Check that the item is removed in the batch.
        assert_eq!(map.get_batched(&0), Some(None));
        // Check that the item is removed when speculatively retrieved.
        assert_eq!(map.get_speculative(&0).unwrap(), None);

        // Finish the current atomic write batch.
        map.finish_atomic().unwrap();

        // Check that the item is not present in the map now.
        assert!(map.get(&0).unwrap().is_none());
        // Check that the item is not in the batch.
        assert_eq!(map.get_batched(&0), None);
        // Check that the item is removed when speculatively retrieved.
        assert_eq!(map.get_speculative(&0).unwrap(), None);

        // Check that the map is empty now.
        assert!(map.iter().next().is_none());
    }

    #[test]
    fn test_atomic_writes_are_batched() {
        // The number of items that will be inserted into the map.
        const NUM_ITEMS: usize = 10;

        // Initialize a map.
        let map: MemoryMap<usize, String> = Default::default();

        // Sanity check.
        assert!(map.iter().next().is_none());

        /* test atomic insertions */

        // Start an atomic write batch.
        map.start_atomic();

        // Queue (since a batch is in progress) NUM_ITEMS insertions.
        for i in 0..NUM_ITEMS {
            map.insert(i, i.to_string()).unwrap();
            // Ensure that the item is queued for insertion.
            assert_eq!(map.get_batched(&i), Some(Some(i.to_string())));
            // Ensure that the item can be found with a speculative get.
            assert_eq!(map.get_speculative(&i).unwrap(), Some(Cow::Owned(i.to_string())));
        }

        // The map should still contain no items.
        assert!(map.iter().next().is_none());

        // Finish the current atomic write batch.
        map.finish_atomic().unwrap();

        // Check that the items are present in the map now.
        for i in 0..NUM_ITEMS {
            assert_eq!(map.get(&i).unwrap(), Some(Cow::Borrowed(&i.to_string())));
        }

        /* test atomic removals */

        // Start an atomic write batch.
        map.start_atomic();

        // Queue (since a batch is in progress) NUM_ITEMS removals.
        for i in 0..NUM_ITEMS {
            map.remove(&i).unwrap();
            // Ensure that the item is NOT queued for insertion.
            assert_eq!(map.get_batched(&i), Some(None));
        }

        // The map should still contains all the items.
        assert_eq!(map.iter().count(), NUM_ITEMS);

        // Finish the current atomic write batch.
        map.finish_atomic().unwrap();

        // Check that the map is empty now.
        assert!(map.iter().next().is_none());
    }

    #[test]
    fn test_atomic_writes_can_be_aborted() {
        // The number of items that will be queued to be inserted into the map.
        const NUM_ITEMS: usize = 10;

        // Initialize a map.
        let map: MemoryMap<usize, String> = Default::default();

        // Sanity check.
        assert!(map.iter().next().is_none());

        // Start an atomic write batch.
        map.start_atomic();

        // Queue (since a batch is in progress) NUM_ITEMS insertions.
        for i in 0..NUM_ITEMS {
            map.insert(i, i.to_string()).unwrap();
        }

        // The map should still contain no items.
        assert!(map.iter().next().is_none());

        // Abort the current atomic write batch.
        map.abort_atomic();

        // The map should still contain no items.
        assert!(map.iter().next().is_none());

        // Start another atomic write batch.
        map.start_atomic();

        // Queue (since a batch is in progress) NUM_ITEMS insertions.
        for i in 0..NUM_ITEMS {
            map.insert(i, i.to_string()).unwrap();
        }

        // Finish the current atomic write batch.
        map.finish_atomic().unwrap();

        // The map should contain NUM_ITEMS items now.
        assert_eq!(map.iter().count(), NUM_ITEMS);
    }
}
