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
use snarkvm_algorithms::merkle_tree::MerklePath;
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::{anyhow, Result};
use itertools::Itertools;
use std::io::{Read, Result as IoResult, Write};

/// A local proof of inclusion for commitments.
#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"), Debug(bound = "N: Network"))]
pub struct LocalProof<N: Network> {
    /// The local commitments root used to prove inclusion of locally-consumed records.
    local_commitments_root: N::LocalCommitmentsRoot,
    commitment_inclusion_proofs: Vec<MerklePath<N::LocalCommitmentsTreeParameters>>,
    commitments: Vec<N::Commitment>,
}

impl<N: Network> LocalProof<N> {
    ///
    /// Initializes a new instance of `LocalProof`, automatically padding inputs as needed.
    ///
    /// This method allows the number of `commitments` and `commitment_inclusion_proofs`
    /// to be less than `N::NUM_INPUT_RECORDS`, as the method will pad up to `N::NUM_INPUT_RECORDS`.
    ///
    pub fn new(
        local_commitments_root: N::LocalCommitmentsRoot,
        commitment_inclusion_proofs: Vec<MerklePath<N::LocalCommitmentsTreeParameters>>,
        commitments: Vec<N::Commitment>,
    ) -> Result<Self> {
        // Ensure the correct number of commitments is given.
        if commitments.len() > N::NUM_INPUT_RECORDS {
            return Err(anyhow!(
                "Incorrect number of given commitments. Expected up to {}, found {}",
                N::NUM_INPUT_RECORDS,
                commitments.len(),
            ));
        }

        // Ensure the correct number of commitment inclusion proofs is given.
        if commitment_inclusion_proofs.len() != commitments.len() {
            return Err(anyhow!(
                "Incorrect number of given commitment inclusion proofs. Expected {}, found {}",
                commitments.len(),
                commitment_inclusion_proofs.len(),
            ));
        }

        // Ensure the commitment inclusion proofs are valid.
        for (commitment_inclusion_proof, commitment) in commitment_inclusion_proofs
            .iter()
            .zip_eq(commitments.iter())
            .take(N::NUM_INPUT_RECORDS)
        {
            if !commitment_inclusion_proof.verify(&local_commitments_root, commitment)? {
                return Err(anyhow!(
                    "Commitment {} does not correspond to root {}",
                    commitment,
                    local_commitments_root
                ));
            }
        }

        // Pad the commitments and commitment inclusion proofs, if necessary.
        let mut commitments = commitments;
        let mut commitment_inclusion_proofs = commitment_inclusion_proofs;
        while commitments.len() < N::NUM_INPUT_RECORDS {
            commitments.push(Default::default());
            commitment_inclusion_proofs.push(Default::default());
        }

        Ok(Self {
            local_commitments_root,
            commitment_inclusion_proofs,
            commitments,
        })
    }

    /// Returns the local commitments root used to prove inclusion of locally-consumed records.
    pub fn local_commitments_root(&self) -> N::LocalCommitmentsRoot {
        self.local_commitments_root
    }

    /// Returns a reference to the commitment inclusion proofs.
    pub fn commitment_inclusion_proofs(&self) -> &Vec<MerklePath<N::LocalCommitmentsTreeParameters>> {
        &self.commitment_inclusion_proofs
    }
}

impl<N: Network> FromBytes for LocalProof<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let local_commitments_root = FromBytes::read_le(&mut reader)?;

        let mut commitment_inclusion_proofs = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            commitment_inclusion_proofs.push(FromBytes::read_le(&mut reader)?);
        }

        let mut commitments = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            commitments.push(FromBytes::read_le(&mut reader)?);
        }

        Ok(
            Self::new(local_commitments_root, commitment_inclusion_proofs, commitments)
                .expect("Failed to deserialize a local state proof"),
        )
    }
}

impl<N: Network> ToBytes for LocalProof<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.local_commitments_root.write_le(&mut writer)?;
        self.commitment_inclusion_proofs.write_le(&mut writer)?;
        self.commitments.write_le(&mut writer)
    }
}

impl<N: Network> Default for LocalProof<N> {
    fn default() -> Self {
        Self {
            local_commitments_root: Default::default(),
            commitment_inclusion_proofs: vec![MerklePath::default(); N::NUM_INPUT_RECORDS],
            commitments: vec![Default::default(); N::NUM_INPUT_RECORDS],
        }
    }
}
