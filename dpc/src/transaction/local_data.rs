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

use crate::{DPCError, LocalDataLeaf, Parameters, Record, RecordScheme, TransactionAuthorization};
use snarkvm_algorithms::{commitment_tree::CommitmentMerkleTree, prelude::*};
use snarkvm_utilities::{FromBytes, ToBytes, UniformRand};

use anyhow::Result;
use rand::{CryptoRng, Rng};
use std::io::{Read, Result as IoResult, Write};

/// The tree of local data commitments for use when executing program proofs.
#[derive(Derivative)]
#[derivative(
    Clone(bound = "C: Parameters"),
    Debug(bound = "C: Parameters"),
    PartialEq(bound = "C: Parameters"),
    Eq(bound = "C: Parameters")
)]
pub struct LocalData<C: Parameters> {
    #[derivative(PartialEq = "ignore", Debug = "ignore")]
    tree: CommitmentMerkleTree<C::LocalDataCommitmentScheme, C::LocalDataCRH>,
    leaves: Vec<LocalDataLeaf<C>>,
    leaf_randomizers: Vec<<C::LocalDataCommitmentScheme as CommitmentScheme>::Randomness>,
}

impl<C: Parameters> LocalData<C> {
    pub fn new<R: Rng + CryptoRng>(
        authorized: &TransactionAuthorization<C>,
        old_records: &Vec<Record<C>>,
        new_records: &Vec<Record<C>>,
        rng: &mut R,
    ) -> Result<Self> {
        let leaves = Self::generate_local_data_leaves(authorized, old_records, new_records);
        Self::from_leaves(leaves, rng)
    }

    pub fn from_leaves<R: Rng + CryptoRng>(leaves: Vec<LocalDataLeaf<C>>, rng: &mut R) -> Result<Self> {
        let leaf_randomizers: Vec<<C::LocalDataCommitmentScheme as CommitmentScheme>::Randomness> =
            (0..C::NUM_TOTAL_RECORDS).map(|_| UniformRand::rand(rng)).collect();
        Self::from(leaves, leaf_randomizers)
    }

    // TODO (raychu86): Add program register inputs + outputs to local data commitment leaves.
    pub fn from(
        leaves: Vec<LocalDataLeaf<C>>,
        leaf_randomizers: Vec<<C::LocalDataCommitmentScheme as CommitmentScheme>::Randomness>,
    ) -> Result<Self> {
        // Ensure the correct number of leaves and randomizers are provided.
        if leaves.len() != C::NUM_TOTAL_RECORDS || leaf_randomizers.len() != C::NUM_TOTAL_RECORDS {
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
            .take(C::NUM_TOTAL_RECORDS)
            .map(|(leaf, randomizer)| {
                C::local_data_commitment_scheme()
                    .commit(
                        &leaf.to_bytes_le().expect("Failed to convert leaf to bytes"),
                        randomizer,
                    )
                    .expect("Failed to compute the leaf commitment")
            })
            .collect::<Vec<_>>();

        // Compute the local data tree.
        let tree = CommitmentMerkleTree::<C::LocalDataCommitmentScheme, _>::new(
            C::local_data_crh().clone(),
            &leaf_commitments,
        )?;

        Ok(Self {
            tree,
            leaves,
            leaf_randomizers,
        })
    }

    pub fn root(&self) -> &<C::LocalDataCRH as CRH>::Output {
        &self.tree.root()
    }

    pub fn leaves(&self) -> &Vec<LocalDataLeaf<C>> {
        &self.leaves
    }

    pub fn leaf_randomizers(&self) -> &Vec<<C::LocalDataCommitmentScheme as CommitmentScheme>::Randomness> {
        &self.leaf_randomizers
    }

    // TODO (raychu86): Add program register inputs + outputs to local data commitment leaves.
    fn generate_local_data_leaves(
        authorized: &TransactionAuthorization<C>,
        old_records: &Vec<Record<C>>,
        new_records: &Vec<Record<C>>,
    ) -> Vec<LocalDataLeaf<C>> {
        let mut leaves = Vec::with_capacity(C::NUM_TOTAL_RECORDS);

        for (i, record) in old_records.iter().enumerate().take(C::NUM_INPUT_RECORDS) {
            leaves.push(LocalDataLeaf::<C>::InputRecord(
                i as u8,
                authorized.serial_numbers[i].clone(),
                record.commitment(),
                authorized.memo,
                C::NETWORK_ID,
            ));
        }

        for (j, record) in new_records.iter().enumerate().take(C::NUM_OUTPUT_RECORDS) {
            leaves.push(LocalDataLeaf::<C>::OutputRecord(
                (C::NUM_OUTPUT_RECORDS + j) as u8,
                record.commitment(),
                authorized.memo,
                C::NETWORK_ID,
            ));
        }

        leaves
    }
}

impl<C: Parameters> ToBytes for LocalData<C> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.leaves.write_le(&mut writer)?;
        self.leaf_randomizers.write_le(&mut writer)
    }
}

impl<C: Parameters> FromBytes for LocalData<C> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let mut leaves = Vec::<LocalDataLeaf<C>>::with_capacity(C::NUM_TOTAL_RECORDS);
        for _ in 0..C::NUM_TOTAL_RECORDS {
            leaves.push(FromBytes::read_le(&mut reader)?);
        }

        let mut leaf_randomizers =
            Vec::<<C::LocalDataCommitmentScheme as CommitmentScheme>::Randomness>::with_capacity(C::NUM_TOTAL_RECORDS);
        for _ in 0..C::NUM_TOTAL_RECORDS {
            leaf_randomizers.push(FromBytes::read_le(&mut reader)?);
        }

        Ok(Self::from(leaves, leaf_randomizers).expect("Unable to create the local data tree"))
    }
}
