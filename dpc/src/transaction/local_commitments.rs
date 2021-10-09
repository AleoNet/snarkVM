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
use snarkvm_algorithms::{merkle_tree::MerkleTree, prelude::*};
use snarkvm_utilities::has_duplicates;

use anyhow::{anyhow, Result};
use std::{collections::HashMap, sync::Arc};

/// A local commitments tree contains all commitments in one transaction.
#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"), Debug(bound = "N: Network"))]
pub(crate) struct LocalCommitments<N: Network> {
    #[derivative(Debug = "ignore")]
    tree: Arc<MerkleTree<N::LocalCommitmentsTreeParameters>>,
    commitments: HashMap<N::Commitment, u8>,
    current_index: u8,
}

impl<N: Network> LocalCommitments<N> {
    /// Initializes an empty local commitments tree.
    pub(crate) fn new() -> Result<Self> {
        Ok(Self {
            tree: Arc::new(MerkleTree::<N::LocalCommitmentsTreeParameters>::new::<N::Commitment>(
                Arc::new(N::local_commitments_tree_parameters().clone()),
                &vec![],
            )?),
            commitments: Default::default(),
            current_index: 0,
        })
    }

    /// TODO (howardwu): Add safety checks for u8 (max 2^8).
    /// Adds the given commitment to the tree, returning its index in the tree.
    pub(crate) fn add(&mut self, commitment: &N::Commitment) -> Result<u8> {
        // Ensure the commitment does not already exist in the tree.
        if self.contains_commitment(commitment) {
            return Err(
                MerkleError::Message(format!("{} already exists in the local commitments tree", commitment)).into(),
            );
        }

        self.tree = Arc::new(self.tree.rebuild(self.current_index as usize, &[commitment])?);

        self.commitments.insert(*commitment, self.current_index);

        self.current_index += 1;
        Ok(self.current_index - 1)
    }

    /// TODO (howardwu): Add safety checks for u8 (max 2^8).
    /// Adds all given commitments to the tree, returning the start and ending index in the tree.
    pub(crate) fn add_all(&mut self, commitments: Vec<N::Commitment>) -> Result<(u8, u8)> {
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
                .map(|(index, commitment)| (commitment, start_index + index as u8)),
        );

        self.current_index += num_commitments as u8;
        let end_index = self.current_index - 1;

        Ok((start_index, end_index))
    }

    /// Returns `true` if the given commitment exists.
    pub(crate) fn contains_commitment(&self, commitment: &N::Commitment) -> bool {
        self.commitments.contains_key(commitment)
    }

    /// Returns the index for the given commitment, if it exists.
    pub(crate) fn get_commitment_index(&self, commitment: &N::Commitment) -> Option<&u8> {
        self.commitments.get(commitment)
    }

    /// Returns the local commitments root.
    pub(crate) fn root(&self) -> N::LocalCommitmentsRoot {
        *self.tree.root()
    }

    /// Returns the local Merkle path for a given commitment.
    pub(crate) fn to_local_proof(&self, commitments: &[N::Commitment]) -> Result<LocalProof<N>> {
        let mut commitment_inclusion_proofs = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for commitment in commitments {
            match self.get_commitment_index(commitment) {
                Some(index) => commitment_inclusion_proofs.push(self.tree.generate_proof(*index as usize, commitment)?),
                _ => return Err(MerkleError::MissingLeaf(format!("{}", commitment)).into()),
            }
        }

        Ok(LocalProof::new(
            self.root(),
            commitment_inclusion_proofs,
            commitments.to_vec(),
        )?)
    }
}

impl<N: Network> Default for LocalCommitments<N> {
    fn default() -> Self {
        Self::new().unwrap()
    }
}
