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

use crate::Transition;
use console::network::prelude::*;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Execution<N: Network>(Vec<Transition<N>>);

impl<N: Network> Execution<N> {
    /// Initialize a new `Execution` instance.
    pub fn new() -> Self {
        Self(Vec::new())
    }

    /// Initializes a new `Execution` instance with the given transitions.
    pub fn from(transitions: &[Transition<N>]) -> Result<Self> {
        // Ensure the transitions is not empty.
        ensure!(!transitions.is_empty(), "Execution cannot initialize from empty list of transitions");
        // Return the new `Execution` instance.
        Ok(Self(transitions.to_vec()))
    }

    /// Returns the `Transition` at the given index.
    pub fn get(&self, index: usize) -> Result<Transition<N>> {
        self.0.get(index).cloned().ok_or_else(|| anyhow!("Attempted to 'get' missing transition {index}"))
    }

    /// Returns the next `Transition` in the execution.
    pub fn peek(&self) -> Result<Transition<N>> {
        self.get(self.len() - 1)
    }

    /// Appends the given `Transition` to the execution.
    pub fn push(&mut self, transition: Transition<N>) {
        self.0.push(transition);
    }

    /// Pops the last `Transition` from the execution.
    pub fn pop(&mut self) -> Result<Transition<N>> {
        self.0.pop().ok_or_else(|| anyhow!("No more transitions in the execution"))
    }
}

impl<N: Network> Deref for Execution<N> {
    type Target = [Transition<N>];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<N: Network> FromStr for Execution<N> {
    type Err = Error;

    /// Initializes the execution from a JSON-string.
    fn from_str(input: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(input)?)
    }
}

impl<N: Network> Debug for Execution<N> {
    /// Prints the execution as a JSON-string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Execution<N> {
    /// Displays the execution as a JSON-string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", serde_json::to_string(self).map_err::<fmt::Error, _>(ser::Error::custom)?)
    }
}
