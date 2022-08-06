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

use crate::ledger::map::{Map, MapRead};
use console::network::prelude::*;
use indexmap::IndexMap;

use core::{borrow::Borrow, hash::Hash};
use indexmap::map;
use parking_lot::RwLock;
use std::{borrow::Cow, sync::Arc};

#[derive(Clone)]
pub struct MemoryMap<
    K: Copy + Clone + PartialEq + Eq + Hash + Serialize + for<'de> Deserialize<'de> + Sync,
    V: Clone + PartialEq + Eq + Serialize + for<'de> Deserialize<'de> + Sync,
> {
    pub(super) map: Arc<RwLock<IndexMap<K, V>>>,
}

impl<
    K: Copy + Clone + PartialEq + Eq + Hash + Serialize + for<'de> Deserialize<'de> + Sync,
    V: Clone + PartialEq + Eq + Serialize + for<'de> Deserialize<'de> + Sync,
> Default for MemoryMap<K, V>
{
    fn default() -> Self {
        Self { map: Default::default() }
    }
}

impl<
    K: Copy + Clone + PartialEq + Eq + Hash + Serialize + for<'de> Deserialize<'de> + Sync,
    V: Clone + PartialEq + Eq + Serialize + for<'de> Deserialize<'de> + Sync,
> FromIterator<(K, V)> for MemoryMap<K, V>
{
    /// Initializes a new `MemoryMap` from the given iterator.
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        Self { map: Arc::new(RwLock::new(IndexMap::from_iter(iter))) }
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
        self.map.write().insert(key, value);

        Ok(())
    }

    ///
    /// Removes the key-value pair for the given key from the map.
    ///
    fn remove<Q>(&self, key: &Q) -> Result<()>
    where
        K: Borrow<Q>,
        Q: PartialEq + Eq + Hash + Serialize + ?Sized,
    {
        self.map.write().remove(key);

        Ok(())
    }
}

impl<
    'a,
    K: 'a + Copy + Clone + PartialEq + Eq + Hash + Serialize + for<'de> Deserialize<'de> + Sync,
    V: 'a + Clone + PartialEq + Eq + Serialize + for<'de> Deserialize<'de> + Sync,
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
    K: Copy + Clone + PartialEq + Eq + Hash + Serialize + for<'de> Deserialize<'de> + Sync,
    V: Clone + PartialEq + Eq + Serialize + for<'de> Deserialize<'de> + Sync,
> Deref for MemoryMap<K, V>
{
    type Target = Arc<RwLock<IndexMap<K, V>>>;

    fn deref(&self) -> &Self::Target {
        &self.map
    }
}
