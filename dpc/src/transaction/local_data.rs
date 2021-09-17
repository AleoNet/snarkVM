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

use crate::{DPCError, LocalDataLeaf, Network, Record, RecordScheme, TransactionKernel};
use snarkvm_algorithms::{commitment_tree::CommitmentMerkleTree, prelude::*};
use snarkvm_utilities::{FromBytes, ToBytes, UniformRand};

use anyhow::Result;
use rand::{CryptoRng, Rng};
use std::io::{Read, Result as IoResult, Write};

/// The tree of local data commitments for use when executing program proofs.
#[derive(Derivative)]
#[derivative(
    Clone(bound = "N: Network"),
    Debug(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network")
)]
pub struct LocalData<N: Network> {
    #[derivative(PartialEq = "ignore", Debug = "ignore")]
    tree: CommitmentMerkleTree<N::LocalDataCommitmentScheme, N::LocalDataCRH>,
    leaves: Vec<LocalDataLeaf<N>>,
    leaf_randomizers: Vec<<N::LocalDataCommitmentScheme as CommitmentScheme>::Randomness>,
}

impl<N: Network> LocalData<N> {
    pub fn new<R: Rng + CryptoRng>(
        kernel: &TransactionKernel<N>,
        input_records: &Vec<Record<N>>,
        output_records: &Vec<Record<N>>,
        rng: &mut R,
    ) -> Result<Self> {
        let leaves = Self::generate_local_data_leaves(kernel, input_records, output_records)?;
        Self::from_leaves(leaves, rng)
    }

    pub fn from_leaves<R: Rng + CryptoRng>(leaves: Vec<LocalDataLeaf<N>>, rng: &mut R) -> Result<Self> {
        let leaf_randomizers: Vec<<N::LocalDataCommitmentScheme as CommitmentScheme>::Randomness> =
            (0..N::NUM_TOTAL_RECORDS).map(|_| UniformRand::rand(rng)).collect();
        Self::from(leaves, leaf_randomizers)
    }

    // TODO (raychu86): Add program register inputs + outputs to local data commitment leaves.
    pub fn from(
        leaves: Vec<LocalDataLeaf<N>>,
        leaf_randomizers: Vec<<N::LocalDataCommitmentScheme as CommitmentScheme>::Randomness>,
    ) -> Result<Self> {
        // Ensure the correct number of leaves and randomizers are provided.
        if leaves.len() != N::NUM_TOTAL_RECORDS || leaf_randomizers.len() != N::NUM_TOTAL_RECORDS {
            return Err(DPCError::Message(format!(
                "Local data size mismatch: leaves - {}, randomizers - {}",
                leaves.len(),
                leaf_randomizers.len()
            ))
            .into());
        }

        // Compute the leaf commitments.
        let leaf_pairs = leaves.iter().zip(leaf_randomizers.iter());
        let leaf_commitments = leaf_pairs
            .take(N::NUM_TOTAL_RECORDS)
            .map(|(leaf, randomizer)| {
                N::local_data_commitment_scheme()
                    .commit(
                        &leaf.to_bytes_le().expect("Failed to convert leaf to bytes"),
                        randomizer,
                    )
                    .expect("Failed to compute the leaf commitment")
            })
            .collect::<Vec<_>>();

        // Compute the local data tree.
        let tree = CommitmentMerkleTree::<N::LocalDataCommitmentScheme, _>::new(
            N::local_data_crh().clone(),
            &leaf_commitments,
        )?;

        Ok(Self {
            tree,
            leaves,
            leaf_randomizers,
        })
    }

    pub fn root(&self) -> &N::LocalDataRoot {
        &self.tree.root()
    }

    pub fn leaves(&self) -> &Vec<LocalDataLeaf<N>> {
        &self.leaves
    }

    pub fn leaf_randomizers(&self) -> &Vec<<N::LocalDataCommitmentScheme as CommitmentScheme>::Randomness> {
        &self.leaf_randomizers
    }

    // TODO (raychu86): Add program register inputs + outputs to local data commitment leaves.
    fn generate_local_data_leaves(
        kernel: &TransactionKernel<N>,
        input_records: &Vec<Record<N>>,
        output_records: &Vec<Record<N>>,
    ) -> Result<Vec<LocalDataLeaf<N>>> {
        // Ensure the correct number of input and output records are provided.
        if input_records.len() != N::NUM_INPUT_RECORDS || output_records.len() != N::NUM_OUTPUT_RECORDS {
            return Err(DPCError::Message(format!(
                "Local data number of records mismatch: input - {}, output - {}",
                input_records.len(),
                output_records.len()
            ))
            .into());
        }

        let mut leaves = Vec::with_capacity(N::NUM_TOTAL_RECORDS);

        for (i, record) in input_records.iter().enumerate().take(N::NUM_INPUT_RECORDS) {
            leaves.push(LocalDataLeaf::<N>::InputRecord(
                i as u8,
                kernel.serial_numbers()[i].clone(),
                record.commitment(),
                kernel.memo().clone(),
                N::NETWORK_ID,
            ));
        }

        for (j, record) in output_records.iter().enumerate().take(N::NUM_OUTPUT_RECORDS) {
            leaves.push(LocalDataLeaf::<N>::OutputRecord(
                (N::NUM_INPUT_RECORDS + j) as u8,
                record.commitment(),
                kernel.memo().clone(),
                N::NETWORK_ID,
            ));
        }

        Ok(leaves)
    }
}

impl<N: Network> ToBytes for LocalData<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.leaves.write_le(&mut writer)?;
        self.leaf_randomizers.write_le(&mut writer)
    }
}

impl<N: Network> FromBytes for LocalData<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let mut leaves = Vec::<LocalDataLeaf<N>>::with_capacity(N::NUM_TOTAL_RECORDS);
        for _ in 0..N::NUM_TOTAL_RECORDS {
            leaves.push(FromBytes::read_le(&mut reader)?);
        }

        let mut leaf_randomizers =
            Vec::<<N::LocalDataCommitmentScheme as CommitmentScheme>::Randomness>::with_capacity(N::NUM_TOTAL_RECORDS);
        for _ in 0..N::NUM_TOTAL_RECORDS {
            leaf_randomizers.push(FromBytes::read_le(&mut reader)?);
        }

        Ok(Self::from(leaves, leaf_randomizers).expect("Unable to create the local data tree"))
    }
}
