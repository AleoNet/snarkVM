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

use snarkvm_console_types::{prelude::*, Field};

use core::ops::{Index, IndexMut, Range};

#[derive(Copy, Clone, Debug)]
pub struct State<E: Environment, const RATE: usize, const CAPACITY: usize> {
    capacity_state: [Field<E>; CAPACITY],
    rate_state: [Field<E>; RATE],
}

impl<E: Environment, const RATE: usize, const CAPACITY: usize> Default for State<E, RATE, CAPACITY> {
    fn default() -> Self {
        Self { capacity_state: [Field::<E>::zero(); CAPACITY], rate_state: [Field::<E>::zero(); RATE] }
    }
}

impl<E: Environment, const RATE: usize, const CAPACITY: usize> State<E, RATE, CAPACITY> {
    /// Returns a reference to a range of the rate state.
    pub(super) fn rate_state(&self, range: Range<usize>) -> &[Field<E>] {
        &self.rate_state[range]
    }

    /// Returns a mutable rate state.
    pub(super) fn rate_state_mut(&mut self) -> &mut [Field<E>; RATE] {
        &mut self.rate_state
    }
}

impl<E: Environment, const RATE: usize, const CAPACITY: usize> State<E, RATE, CAPACITY> {
    /// Returns an immutable iterator over the state.
    pub fn iter(&self) -> impl Iterator<Item = &Field<E>> {
        self.capacity_state.iter().chain(self.rate_state.iter())
    }

    /// Returns an mutable iterator over the state.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Field<E>> {
        self.capacity_state.iter_mut().chain(self.rate_state.iter_mut())
    }
}

impl<E: Environment, const RATE: usize, const CAPACITY: usize> Index<usize> for State<E, RATE, CAPACITY> {
    type Output = Field<E>;

    fn index(&self, index: usize) -> &Self::Output {
        assert!(index < RATE + CAPACITY, "Index out of bounds: index is {} but length is {}", index, RATE + CAPACITY);
        if index < CAPACITY { &self.capacity_state[index] } else { &self.rate_state[index - CAPACITY] }
    }
}

impl<E: Environment, const RATE: usize, const CAPACITY: usize> IndexMut<usize> for State<E, RATE, CAPACITY> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        assert!(index < RATE + CAPACITY, "Index out of bounds: index is {} but length is {}", index, RATE + CAPACITY);
        if index < CAPACITY { &mut self.capacity_state[index] } else { &mut self.rate_state[index - CAPACITY] }
    }
}
