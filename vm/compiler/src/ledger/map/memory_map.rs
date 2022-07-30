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

use crate::ledger::map::{Map, MapReader};
use console::network::prelude::*;

use core::{borrow::Borrow, hash::Hash};
use std::collections::hash_map::{HashMap, Iter, Keys, Values};

#[derive(Clone)]
pub struct MemoryMap<
    K: PartialEq + Eq + Hash + Serialize + DeserializeOwned,
    V: PartialEq + Eq + Serialize + DeserializeOwned,
> {
    pub(super) map: HashMap<K, V>,
}

impl<
    K: PartialEq + Eq + Hash + Serialize + DeserializeOwned + Clone,
    V: PartialEq + Eq + Serialize + DeserializeOwned + Clone,
> FromIterator<(K, V)> for MemoryMap<K, V>
{
    /// Initializes a new `MemoryMap` from the given iterator.
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        Self { map: HashMap::from_iter(iter) }
    }
}

impl<
    'a,
    K: PartialEq + Eq + Hash + Serialize + DeserializeOwned + Clone + 'a,
    V: PartialEq + Eq + Serialize + DeserializeOwned + Clone + 'a,
> Map<'a, K, V> for MemoryMap<K, V>
{
    ///
    /// Inserts the given key-value pair into the map.
    ///
    fn insert<Q>(&mut self, key: K, value: V) -> Result<()>
    where
        Q: PartialEq + Eq + Hash + Serialize,
    {
        self.map.insert(key, value);

        Ok(())
    }

    ///
    /// Removes the key-value pair for the given key from the map.
    ///
    fn remove<Q>(&mut self, key: &Q) -> Result<()>
    where
        K: Borrow<Q>,
        Q: PartialEq + Eq + Hash + Serialize + ?Sized,
    {
        self.map.remove(key);

        Ok(())
    }
}

impl<
    'a,
    K: PartialEq + Eq + Hash + Serialize + DeserializeOwned + Clone + 'a,
    V: PartialEq + Eq + Serialize + DeserializeOwned + Clone + 'a,
> MapReader<'a, K, V> for MemoryMap<K, V>
{
    type Iterator = Iter<'a, K, V>;
    type Keys = Keys<'a, K, V>;
    type Values = Values<'a, K, V>;

    ///
    /// Returns `true` if the given key exists in the map.
    ///
    fn contains_key<Q>(&self, key: &Q) -> Result<bool>
    where
        K: Borrow<Q>,
        Q: PartialEq + Eq + Hash + Serialize + ?Sized,
    {
        Ok(self.map.contains_key(key))
    }

    ///
    /// Returns the value for the given key from the map, if it exists.
    ///
    fn get<Q>(&self, key: &Q) -> Result<Option<&V>>
    where
        K: Borrow<Q>,
        Q: PartialEq + Eq + Hash + Serialize + ?Sized,
    {
        Ok(self.map.get(key))
    }

    // TODO (raychu86): This is extremely inefficient due to cloning as a workaround for lifetimes.

    ///
    /// Returns an iterator visiting each key-value pair in the map.
    ///
    fn iter(&'a self) -> Self::Iterator {
        self.map.iter()
    }

    ///
    /// Returns an iterator over each key in the map.
    ///
    fn keys(&'a self) -> Self::Keys {
        self.map.keys()
    }

    ///
    /// Returns an iterator over each value in the map.
    ///
    fn values(&'a self) -> Self::Values {
        self.map.values()
    }
}

impl<
    K: PartialEq + Eq + Hash + Serialize + DeserializeOwned + Clone,
    V: PartialEq + Eq + Serialize + DeserializeOwned + Clone,
> Default for MemoryMap<K, V>
{
    fn default() -> Self {
        Self { map: HashMap::new() }
    }
}
