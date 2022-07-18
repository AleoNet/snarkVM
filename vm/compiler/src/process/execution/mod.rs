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

mod bytes;
mod serialize;
mod string;

use crate::Transition;
use console::network::prelude::*;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Execution<N: Network> {
    /// The edition.
    edition: u16,
    /// The transitions.
    transitions: Vec<Transition<N>>,
}

impl<N: Network> Execution<N> {
    /// Initialize a new `Execution` instance.
    pub fn new() -> Self {
        Self { edition: N::EDITION, transitions: Vec::new() }
    }

    /// Initializes a new `Execution` instance with the given transitions.
    pub fn from(edition: u16, transitions: &[Transition<N>]) -> Result<Self> {
        // Ensure the transitions is not empty.
        ensure!(!transitions.is_empty(), "Execution cannot initialize from empty list of transitions");
        // Return the new `Execution` instance.
        match edition == N::EDITION {
            true => Ok(Self { edition, transitions: transitions.to_vec() }),
            false => bail!("Execution cannot initialize with a different edition"),
        }
    }

    /// Returns the edition.
    pub const fn edition(&self) -> u16 {
        self.edition
    }
}

impl<N: Network> Execution<N> {
    /// Returns the `Transition` at the given index.
    pub fn get(&self, index: usize) -> Result<Transition<N>> {
        self.transitions.get(index).cloned().ok_or_else(|| anyhow!("Attempted to 'get' missing transition {index}"))
    }

    /// Returns the next `Transition` in the execution.
    pub fn peek(&self) -> Result<Transition<N>> {
        self.get(self.len() - 1)
    }

    /// Appends the given `Transition` to the execution.
    pub fn push(&mut self, transition: Transition<N>) {
        self.transitions.push(transition);
    }

    /// Pops the last `Transition` from the execution.
    pub fn pop(&mut self) -> Result<Transition<N>> {
        self.transitions.pop().ok_or_else(|| anyhow!("No more transitions in the execution"))
    }
}

impl<N: Network> Deref for Execution<N> {
    type Target = [Transition<N>];

    fn deref(&self) -> &Self::Target {
        &self.transitions
    }
}
