// Copyright (C) 2019-2023 Aleo Systems Inc.
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

use crate::{snark::Proof, Transition};
use console::{account::Field, network::prelude::*};

use indexmap::IndexMap;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Execution<N: Network> {
    /// The transitions.
    transitions: IndexMap<N::TransitionID, Transition<N>>,
    /// The global state root.
    global_state_root: N::StateRoot,
    /// The inclusion proof.
    inclusion_proof: Option<Proof<N>>,
}

impl<N: Network> Execution<N> {
    /// Initialize a new `Execution` instance.
    pub fn new() -> Self {
        Self { transitions: Default::default(), global_state_root: Default::default(), inclusion_proof: None }
    }

    /// Initializes a new `Execution` instance with the given transitions.
    pub fn from(
        transitions: impl Iterator<Item = Transition<N>>,
        global_state_root: N::StateRoot,
        inclusion_proof: Option<Proof<N>>,
    ) -> Result<Self> {
        // Construct the execution.
        let execution =
            Self { transitions: transitions.map(|t| (*t.id(), t)).collect(), global_state_root, inclusion_proof };
        // Ensure the transitions are not empty.
        ensure!(!execution.transitions.is_empty(), "Execution cannot initialize from empty list of transitions");
        // Return the new `Execution` instance.
        Ok(execution)
    }

    /// Returns the size in bytes.
    pub fn size_in_bytes(&self) -> Result<u64> {
        Ok(u64::try_from(self.to_bytes_le()?.len())?)
    }

    /// Returns the global state root.
    pub const fn global_state_root(&self) -> N::StateRoot {
        self.global_state_root
    }

    /// Returns the inclusion proof.
    pub const fn inclusion_proof(&self) -> Option<&Proof<N>> {
        self.inclusion_proof.as_ref()
    }
}

impl<N: Network> Execution<N> {
    /// Returns `true` if the execution contains the transition for the given transition ID.
    pub fn contains_transition(&self, transition_id: &N::TransitionID) -> bool {
        self.transitions.contains_key(transition_id)
    }

    /// Returns the `Transition` corresponding to the given transition ID. This method is `O(1)`.
    pub fn find_transition(&self, id: &N::TransitionID) -> Option<&Transition<N>> {
        self.transitions.get(id)
    }

    /// Returns the `Transition` at the given index.
    pub fn get(&self, index: usize) -> Result<&Transition<N>> {
        match self.transitions.get_index(index) {
            Some((_, transition)) => Ok(transition),
            None => bail!("Transition index {index} out of bounds in the execution object"),
        }
    }

    /// Returns the next `Transition` in the execution.
    pub fn peek(&self) -> Result<&Transition<N>> {
        self.get(self.len() - 1)
    }

    /// Appends the given `Transition` to the execution.
    pub fn push(&mut self, transition: Transition<N>) {
        self.transitions.insert(*transition.id(), transition);
    }

    /// Pops the last `Transition` from the execution.
    pub fn pop(&mut self) -> Result<Transition<N>> {
        match self.transitions.pop() {
            Some((_, transition)) => Ok(transition),
            None => bail!("Cannot pop a transition from an empty execution object"),
        }
    }

    /// Returns the number of transitions in the execution.
    pub fn len(&self) -> usize {
        self.transitions.len()
    }

    /// Returns `true` if the execution is empty.
    pub fn is_empty(&self) -> bool {
        self.transitions.is_empty()
    }
}

impl<N: Network> Execution<N> {
    /// Returns a consuming iterator over the underlying transitions.
    pub fn into_transitions(self) -> impl ExactSizeIterator + DoubleEndedIterator<Item = Transition<N>> {
        self.transitions.into_values()
    }

    /// Returns an iterator over the underlying transitions.
    pub fn transitions(&self) -> impl '_ + ExactSizeIterator + DoubleEndedIterator<Item = &Transition<N>> {
        self.transitions.values()
    }

    /// Returns an iterator over the commitments.
    pub fn commitments(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transitions.values().flat_map(Transition::commitments)
    }
}
