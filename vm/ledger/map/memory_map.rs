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

use crate::{
    console::network::prelude::*,
    ledger::map::{Map, MapReader},
};

use core::borrow::Borrow;
// use std::collections::hash_map::HashMap;
use std::{
    collections::hash_map::{HashMap, IntoIter, IntoKeys, IntoValues},
    // collections::hash_map::{HashMap, Iter, Keys, Values},
    hash::Hash,
    sync::Arc,
};

#[derive(Clone)]
pub struct MemoryMap<
    K: PartialEq + Eq + Hash + Serialize + DeserializeOwned,
    V: PartialEq + Eq + Serialize + DeserializeOwned,
> {
    pub(super) map: HashMap<K, V>,
}

impl<'a, K: PartialEq + Eq + Hash + Serialize + DeserializeOwned, V: PartialEq + Eq + Serialize + DeserializeOwned>
    Map<'a, K, V> for MemoryMap<K, V>
{
    //TODO (raychu86): Find a fix for `insert` and `remove` not having a mutable self.

    ///
    /// Inserts the given key-value pair into the map.
    ///
    fn insert<Q>(&self, key: Q, value: V) -> Result<()>
    where
        K: Borrow<Q>,
        Q: PartialEq + Eq + Hash + Serialize + Serialize,
    {
        // TODO (raychu86): FIX THIS.

        // let k = (key as &dyn std::any::Any).downcast_ref::<K>().unwrap();
        // self.map.insert(k, value);

        // (&$variable as &dyn std::any::Any).downcast_ref::<$object<$network>>()

        self.map.insert(*key, value);

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
        self.map.remove(key);

        Ok(())
    }
}

impl<'a, K: PartialEq + Eq + Hash + Serialize + DeserializeOwned, V: PartialEq + Eq + Serialize + DeserializeOwned>
    MapReader<'a, K, V> for MemoryMap<K, V>
{
    // TODO (raychu86): There is a lifetime issue with using standard `Iter`, `Keys`, and `Values` because the traits
    //  expect owned objects.
    type Iterator = IntoIter<K, V>;
    type Keys = IntoKeys<K, V>;
    type Values = IntoValues<K, V>;

    // type Iterator = Iter<'a, K, V>;
    // type Keys = Keys<'a, K, V>;
    // type Values = Values<'a, K, V>;

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

    ///
    /// Returns an iterator visiting each key-value pair in the map.
    ///
    fn iter(&'a self) -> Self::Iterator {
        self.map.into_iter()
    }

    ///
    /// Returns an iterator over each key in the map.
    ///
    fn keys(&'a self) -> Self::Keys {
        self.map.into_keys()
    }

    ///
    /// Returns an iterator over each value in the map.
    ///
    fn values(&'a self) -> Self::Values {
        self.map.into_values()
    }
}
