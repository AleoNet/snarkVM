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

// A helper object containing a list of values that, when removed, leave a "hole" in their
// place; this allows all the following indices to remain unperturbed; the holes take priority
// when inserting new objects.
pub struct OptionalVec<T> {
    // a list of optional values
    values: Vec<Option<T>>,
    // a list of indices of the Nones in the values vector
    holes: Vec<usize>,
}

impl<T> Default for OptionalVec<T> {
    fn default() -> Self {
        Self { values: Default::default(), holes: Default::default() }
    }
}

impl<T> OptionalVec<T> {
    /// Creates a new `OptionalVec` with the given underlying capacity.
    #[inline]
    pub fn with_capacity(cap: usize) -> Self {
        Self { values: Vec::with_capacity(cap), holes: Default::default() }
    }

    /// Inserts a new value either into the first existing hole or extending the vector
    /// of values, i.e. pushing it to its end.
    #[inline]
    pub fn insert(&mut self, elem: T) -> usize {
        let idx = self.holes.pop().unwrap_or(self.values.len());
        if idx < self.values.len() {
            self.values[idx] = Some(elem);
        } else {
            self.values.push(Some(elem));
        }
        idx
    }

    /// Returns the index of the next value inserted into the `OptionalVec`.
    #[inline]
    pub fn next_idx(&self) -> usize {
        self.holes.last().copied().unwrap_or(self.values.len())
    }

    /// Removes a value at the specified index; assumes that the index points to
    /// an existing value that is a `Some(T)` (i.e. not a hole).
    #[inline]
    pub fn remove(&mut self, idx: usize) -> T {
        let val = self.values[idx].take();
        self.holes.push(idx);
        val.unwrap()
    }

    /// Iterates over all the `Some(T)` values in the list.
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.values.iter().filter_map(|v| v.as_ref())
    }

    /// Returns the number of `Some(T)` values.
    #[inline]
    pub fn len(&self) -> usize {
        self.values.len() - self.holes.len()
    }

    #[inline]
    /// Returns `true` if there are no `Some(T)` values
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T> std::ops::Index<usize> for OptionalVec<T> {
    type Output = T;

    fn index(&self, idx: usize) -> &Self::Output {
        self.values[idx].as_ref().unwrap()
    }
}

impl<T> std::ops::IndexMut<usize> for OptionalVec<T> {
    fn index_mut(&mut self, idx: usize) -> &mut Self::Output {
        self.values[idx].as_mut().unwrap()
    }
}
