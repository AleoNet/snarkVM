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

use std::{borrow::Cow, collections::hash_map};

/// An iterator over all key-value pairs in a MemoryMap.
pub struct Iter<'a, K: 'a + Clone, V: 'a + Clone> {
    pub(crate) inner: hash_map::Iter<'a, K, V>,
}

impl<'a, K: 'a + Clone, V: 'a + Clone> Iter<'a, K, V> {
    #[inline]
    pub(crate) fn new(inner: hash_map::Iter<'a, K, V>) -> Self {
        Self { inner }
    }
}

impl<'a, K: 'a + Clone, V: 'a + Clone> Iterator for Iter<'a, K, V> {
    type Item = (Cow<'a, K>, Cow<'a, V>);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, v)| (Cow::Borrowed(k), Cow::Borrowed(v)))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// An iterator over the keys in a MemoryMap.
pub struct Keys<'a, K: 'a + Clone, V: 'a + Clone> {
    inner: Iter<'a, K, V>,
}

impl<'a, K: 'a + Clone, V: 'a + Clone> Keys<'a, K, V> {
    #[inline]
    pub(crate) fn new(inner: Iter<'a, K, V>) -> Self {
        Self { inner }
    }
}

impl<'a, K: 'a + Clone, V: 'a + Clone> Iterator for Keys<'a, K, V> {
    type Item = Cow<'a, K>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, _)| k)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// An iterator over the value in a MemoryMap.
pub struct Values<'a, K: 'a + Clone, V: 'a + Clone> {
    inner: Iter<'a, K, V>,
}

impl<'a, K: 'a + Clone, V: 'a + Clone> Values<'a, K, V> {
    #[inline]
    pub(crate) fn new(inner: Iter<'a, K, V>) -> Self {
        Self { inner }
    }
}

impl<'a, K: 'a + Clone, V: 'a + Clone> Iterator for Values<'a, K, V> {
    type Item = Cow<'a, V>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}
