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

use super::*;

use std::borrow::Cow;
use tracing::error;

/// An iterator over all key-value pairs in a data map.
pub struct Iter<
    'a,
    K: 'a + Debug + PartialEq + Eq + Hash + Serialize + DeserializeOwned,
    V: 'a + PartialEq + Eq + Serialize + DeserializeOwned,
> {
    db_iter: rocksdb::DBIterator<'a>,
    _phantom: PhantomData<(K, V)>,
}

impl<
    'a,
    K: 'a + Debug + PartialEq + Eq + Hash + Serialize + DeserializeOwned,
    V: 'a + PartialEq + Eq + Serialize + DeserializeOwned,
> Iter<'a, K, V>
{
    pub(super) fn new(db_iter: rocksdb::DBIterator<'a>) -> Self {
        Self { db_iter, _phantom: PhantomData }
    }
}

impl<
    'a,
    K: 'a + Clone + Debug + PartialEq + Eq + Hash + Serialize + DeserializeOwned,
    V: 'a + Clone + PartialEq + Eq + Serialize + DeserializeOwned,
> Iterator for Iter<'a, K, V>
{
    type Item = (Cow<'a, K>, Cow<'a, V>);

    fn next(&mut self) -> Option<Self::Item> {
        let (key, value) = self
            .db_iter
            .next()?
            .map_err(|e| {
                error!("RocksDB iterator error: {e}");
            })
            .ok()?;
        let key = bincode::deserialize(&key[PREFIX_LEN..]).ok()?;
        let value = bincode::deserialize(&value).ok()?;

        Some((Cow::Owned(key), Cow::Owned(value)))
    }
}

/// An iterator over the keys of a prefix.
pub struct Keys<'a, K: 'a + Debug + PartialEq + Eq + Hash + Serialize + DeserializeOwned> {
    db_iter: rocksdb::DBIterator<'a>,
    _phantom: PhantomData<K>,
}

impl<'a, K: 'a + Debug + PartialEq + Eq + Hash + Serialize + DeserializeOwned> Keys<'a, K> {
    pub(crate) fn new(db_iter: rocksdb::DBIterator<'a>) -> Self {
        Self { db_iter, _phantom: PhantomData }
    }
}

impl<'a, K: 'a + Clone + Debug + PartialEq + Eq + Hash + Serialize + DeserializeOwned> Iterator for Keys<'a, K> {
    type Item = Cow<'a, K>;

    fn next(&mut self) -> Option<Self::Item> {
        let (key, _) = self
            .db_iter
            .next()?
            .map_err(|e| {
                error!("RocksDB iterator error: {e}");
            })
            .ok()?;
        let key = bincode::deserialize(&key[PREFIX_LEN..]).ok()?;

        Some(Cow::Owned(key))
    }
}

/// An iterator over the values of a prefix.
pub struct Values<'a, V: 'a + PartialEq + Eq + Serialize + DeserializeOwned> {
    db_iter: rocksdb::DBIterator<'a>,
    _phantom: PhantomData<V>,
}

impl<'a, V: 'a + PartialEq + Eq + Serialize + DeserializeOwned> Values<'a, V> {
    pub(crate) fn new(db_iter: rocksdb::DBIterator<'a>) -> Self {
        Self { db_iter, _phantom: PhantomData }
    }
}

impl<'a, V: 'a + Clone + PartialEq + Eq + Serialize + DeserializeOwned> Iterator for Values<'a, V> {
    type Item = Cow<'a, V>;

    fn next(&mut self) -> Option<Self::Item> {
        let (_, value) = self
            .db_iter
            .next()?
            .map_err(|e| {
                error!("RocksDB iterator error: {e}");
            })
            .ok()?;
        let value = bincode::deserialize(&value).ok()?;

        Some(Cow::Owned(value))
    }
}
