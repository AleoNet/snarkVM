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

pub mod memory_map;

use crate::console::network::prelude::*;

use core::borrow::Borrow;
use std::hash::Hash;

/// A trait representing map-like storage operations with read-write capabilities.
pub trait Map<
    'a,
    K: PartialEq + Eq + Hash + Serialize + DeserializeOwned + 'a,
    V: PartialEq + Eq + Serialize + DeserializeOwned + 'a,
>: MapReader<'a, K, V> + FromIterator<(K, V)>
{
    ///
    /// Inserts the given key-value pair into the map.
    ///
    fn insert<Q>(&mut self, key: K, value: V) -> Result<()>
    where
        Q: PartialEq + Eq + Hash + Serialize;

    ///
    /// Removes the key-value pair for the given key from the map.
    ///
    fn remove<Q>(&mut self, key: &Q) -> Result<()>
    where
        K: Borrow<Q>,
        Q: PartialEq + Eq + Hash + Serialize + ?Sized;
}

/// A trait representing map-like storage operations with read-only capabilities.
pub trait MapReader<
    'a,
    K: PartialEq + Eq + Hash + Serialize + DeserializeOwned + 'a,
    V: PartialEq + Eq + Serialize + DeserializeOwned + 'a,
>
{
    type Iterator: Iterator<Item = (&'a K, &'a V)>;
    type Keys: Iterator<Item = &'a K>;
    type Values: Iterator<Item = &'a V>;

    ///
    /// Returns `true` if the given key exists in the map.
    ///
    fn contains_key<Q>(&self, key: &Q) -> Result<bool>
    where
        K: Borrow<Q>,
        Q: PartialEq + Eq + Hash + Serialize + ?Sized;

    ///
    /// Returns the value for the given key from the map, if it exists.
    ///
    fn get<Q>(&self, key: &Q) -> Result<Option<&V>>
    where
        K: Borrow<Q>,
        Q: PartialEq + Eq + Hash + Serialize + ?Sized;

    ///
    /// Returns an iterator visiting each key-value pair in the map.
    ///
    fn iter(&'a self) -> Self::Iterator;

    ///
    /// Returns an iterator over each key in the map.
    ///
    fn keys(&'a self) -> Self::Keys;

    ///
    /// Returns an iterator over each value in the map.
    ///
    fn values(&'a self) -> Self::Values;
}
