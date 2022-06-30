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

use crate::prelude::*;
use snarkvm_algorithms::{merkle_tree::*, prelude::*};
use snarkvm_utilities::has_duplicates;

use anyhow::{anyhow, Result};
use std::{collections::HashMap, sync::Arc};

/// A local transitions tree contains all the transitions for one transaction.
#[derive(Clone, Derivative)]
#[derivative(Debug(bound = "N: Network"))]
pub(crate) struct Transitions<N: Network> {
    #[derivative(Debug = "ignore")]
    tree: Arc<MerkleTree<N::TransactionIDParameters>>,
    transitions: HashMap<N::TransitionID, (u8, Transition<N>)>,
    current_index: u8,
}

impl<N: Network> Transitions<N> {
    /// Initializes an empty local transitions tree.
    pub(crate) fn new() -> Result<Self> {
        Ok(Self {
            tree: Arc::new(MerkleTree::<N::TransactionIDParameters>::new::<N::TransitionID>(
                Arc::new(N::transaction_id_parameters().clone()),
                &[],
            )?),
            transitions: Default::default(),
            current_index: 0,
        })
    }

    /// Adds the given transition to the tree, returning its index in the tree.
    pub(crate) fn add(&mut self, transition: &Transition<N>) -> Result<u8> {
        // Ensure the transition does not already exist in the tree.
        let transition_id = transition.transition_id();
        if self.contains_transition(&transition_id) {
            return Err(
                MerkleError::Message(format!("{} already exists in the transitions tree", transition_id)).into()
            );
        }

        // Ensure the current index has not reached the maximum number of transitions permitted in software.
        if self.current_index >= N::NUM_TRANSITIONS {
            return Err(anyhow!("The transitions tree has reached its maximum size"));
        }

        self.tree = Arc::new(self.tree.rebuild(self.current_index as usize, &[transition_id])?);
        self.transitions.insert(transition_id, (self.current_index, transition.clone()));
        let current_index = self.current_index;
        self.current_index = current_index
            .checked_add(1)
            .ok_or_else(|| anyhow!("The index exceeds the maximum number of allowed transitions."))?;

        Ok(current_index)
    }

    /// Adds all given transitions to the tree, returning the start and ending index in the tree.
    pub(crate) fn add_all(&mut self, transitions: &[Transition<N>]) -> Result<(u8, u8)> {
        // Ensure the current index has not reached the maximum number of transitions permitted in software.
        if self.current_index >= N::NUM_TRANSITIONS
            || (self.current_index as usize).saturating_add(transitions.len()) >= N::NUM_TRANSITIONS as usize
        {
            return Err(anyhow!("The transitions tree has reached its maximum size"));
        }

        // Ensure the list of given transitions is unique.
        let transition_ids = transitions.iter().map(Transition::transition_id).collect::<Vec<_>>();
        if has_duplicates(transition_ids.iter()) {
            return Err(anyhow!("The list of given transitions contains duplicates"));
        }

        // Ensure the transitions do not already exist in the tree.
        let num_duplicates = transition_ids.iter().filter(|id| self.contains_transition(id)).count();
        if num_duplicates > 0 {
            return Err(anyhow!("The list of given transitions contains double spends"));
        }

        let start_index = self.current_index;
        self.tree = Arc::new(self.tree.rebuild(self.current_index as usize, &transition_ids)?);
        self.transitions.extend(
            transitions
                .iter()
                .cloned()
                .enumerate()
                .map(|(index, transition)| (transition.transition_id(), (start_index + index as u8, transition))),
        );
        self.current_index = self
            .current_index
            .checked_add(transition_ids.len() as u8)
            .ok_or_else(|| anyhow!("The index exceeds the maximum number of allowed transitions."))?;
        let end_index = self.current_index.checked_sub(1).ok_or_else(|| anyhow!("Integer underflow."))?;

        Ok((start_index, end_index))
    }

    /// Returns `true` if the given transition exists.
    pub(crate) fn contains_transition(&self, transition_id: &N::TransitionID) -> bool {
        self.transitions.contains_key(transition_id)
    }

    /// Returns the index for the given transition, if it exists.
    pub(crate) fn get_transition_index(&self, transition_id: &N::TransitionID) -> Option<&u8> {
        self.transitions.get(transition_id).map(|(index, _)| index)
    }

    /// Returns the local transitions root.
    pub(crate) fn root(&self) -> N::TransactionID {
        (*self.tree.root()).into()
    }

    /// Returns the size of the local transitions tree.
    pub(crate) fn len(&self) -> usize {
        self.current_index as usize
    }

    /// Returns the local proof for a given commitment.
    pub(crate) fn to_local_proof(&self, commitment: N::Commitment) -> Result<LocalProof<N>> {
        let (_, (_, transition)) = match self
            .transitions
            .iter()
            .filter(|(_, (_, transition))| transition.contains_commitment(&commitment))
            .last()
        {
            Some(tuple) => tuple,
            None => return Err(MerkleError::MissingLeaf(format!("{}", commitment)).into()),
        };

        let transition_id = transition.transition_id();
        let transition_inclusion_proof = transition.to_transition_inclusion_proof(commitment)?;
        let transaction_id = self.root();
        let transaction_inclusion_proof = self.to_transition_path(transition_id)?;

        LocalProof::new(
            transaction_id,
            transaction_inclusion_proof,
            transition_id,
            transition_inclusion_proof,
            commitment,
        )
    }

    /// Returns the Merkle path for a given transition.
    fn to_transition_path(&self, transition_id: N::TransitionID) -> Result<MerklePath<N::TransactionIDParameters>> {
        match self.get_transition_index(&transition_id) {
            Some(index) => Ok(self.tree.generate_proof(*index as usize, &transition_id)?),
            _ => Err(MerkleError::MissingLeaf(format!("{}", transition_id)).into()),
        }
    }
}
