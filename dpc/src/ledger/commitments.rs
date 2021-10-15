// Copyright (C) 2019-2021 Aleo Systems Inc.
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
use snarkvm_algorithms::{
    merkle_tree::{MerklePath, MerkleTree},
    prelude::*,
};
use snarkvm_utilities::has_duplicates;

use anyhow::{anyhow, Result};
use std::{collections::HashMap, sync::Arc};

/// A commitments tree contains all commitments on the ledger.
#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"), Debug(bound = "N: Network"))]
pub struct Commitments<N: Network> {
    #[derivative(Debug = "ignore")]
    tree: Arc<MerkleTree<N::CommitmentsTreeParameters>>,
    commitments: HashMap<N::Commitment, u64>,
    current_index: u64,
}

impl<N: Network> CommitmentsTreeScheme<N> for Commitments<N> {
    /// Initializes an empty commitments tree.
    fn new() -> Result<Self> {
        Ok(Self {
            tree: Arc::new(MerkleTree::<N::CommitmentsTreeParameters>::new::<N::Commitment>(
                Arc::new(N::commitments_tree_parameters().clone()),
                &vec![],
            )?),
            commitments: Default::default(),
            current_index: 0,
        })
    }

    /// TODO (howardwu): Add safety checks for u64 (max 2^42).
    /// Adds the given commitment to the tree, returning its index in the tree.
    fn add(&mut self, commitment: &N::Commitment) -> Result<u64> {
        // Ensure the commitment does not already exist in the tree.
        if self.contains_commitment(commitment) {
            return Err(MerkleError::Message(format!("{} already exists in the commitments tree", commitment)).into());
        }

        self.tree = Arc::new(self.tree.rebuild(self.current_index as usize, &[commitment])?);

        self.commitments.insert(*commitment, self.current_index);

        self.current_index += 1;
        Ok(self.current_index - 1)
    }

    /// TODO (howardwu): Add safety checks for u64 (max 2^42).
    /// Adds all given commitments to the tree, returning the start and ending index in the tree.
    fn add_all(&mut self, commitments: &[N::Commitment]) -> Result<(u64, u64)> {
        // Ensure the list of given commitments is non-empty.
        if commitments.is_empty() {
            return Err(anyhow!("The list of given commitments must be non-empty"));
        }

        // Ensure the list of given commitments is unique.
        if has_duplicates(commitments.iter()) {
            return Err(anyhow!("The list of given commitments contains duplicates"));
        }

        // Ensure the commitments do not already exist in the tree.
        let duplicate_commitments: Vec<_> = commitments.iter().filter(|c| self.contains_commitment(c)).collect();
        if !duplicate_commitments.is_empty() {
            return Err(anyhow!("The list of given commitments contains double spends"));
        }

        self.tree = Arc::new(self.tree.rebuild(self.current_index as usize, &commitments)?);

        let start_index = self.current_index;
        let num_commitments = commitments.len();

        self.commitments.extend(
            commitments
                .into_iter()
                .enumerate()
                .map(|(index, commitment)| (*commitment, start_index + index as u64)),
        );

        self.current_index += num_commitments as u64;
        let end_index = self.current_index - 1;

        Ok((start_index, end_index))
    }

    /// Returns `true` if the given commitment exists.
    fn contains_commitment(&self, commitment: &N::Commitment) -> bool {
        self.commitments.contains_key(commitment)
    }

    /// Returns the index for the given commitment, if it exists.
    fn get_commitment_index(&self, commitment: &N::Commitment) -> Option<&u64> {
        self.commitments.get(commitment)
    }

    /// Returns the commitments root.
    fn root(&self) -> N::CommitmentsRoot {
        *self.tree.root()
    }

    /// Returns the Merkle path for a given commitment.
    fn to_commitment_inclusion_proof(
        &self,
        commitment: &N::Commitment,
    ) -> Result<MerklePath<N::CommitmentsTreeParameters>> {
        match self.get_commitment_index(commitment) {
            Some(index) => Ok(self.tree.generate_proof(*index as usize, commitment)?),
            _ => Err(MerkleError::MissingLeaf(format!("{}", commitment)).into()),
        }
    }
}

impl<N: Network> Default for Commitments<N> {
    fn default() -> Self {
        Self::new().unwrap()
    }
}
