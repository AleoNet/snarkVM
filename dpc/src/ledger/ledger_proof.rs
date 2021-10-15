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
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::{anyhow, Result};
use itertools::Itertools;
use std::{
    io::{Read, Result as IoResult, Write},
    sync::Arc,
};

/// A ledger proof of inclusion.
#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"), Debug(bound = "N: Network"))]
pub struct LedgerProof<N: Network> {
    /// The block hash used to prove inclusion of ledger-consumed records.
    block_hash: N::BlockHash,
    previous_block_hash: N::BlockHash,
    header_root: N::BlockHeaderRoot,
    header_inclusion_proof: MerklePath<N::BlockHeaderTreeParameters>,
    commitments_root: N::CommitmentsRoot,
    commitment_inclusion_proofs: Vec<MerklePath<N::CommitmentsTreeParameters>>,
    commitments: Vec<N::Commitment>,
}

impl<N: Network> LedgerProof<N> {
    ///
    /// Initializes a new instance of `LedgerProof`, automatically padding inputs as needed.
    ///
    /// This method allows the number of `commitments` and `commitment_inclusion_proofs`
    /// to be less than `N::NUM_INPUT_RECORDS`, as the method will pad up to `N::NUM_INPUT_RECORDS`.
    ///
    pub fn new(
        block_hash: N::BlockHash,
        previous_block_hash: N::BlockHash,
        header_root: N::BlockHeaderRoot,
        header_inclusion_proof: MerklePath<N::BlockHeaderTreeParameters>,
        commitments_root: N::CommitmentsRoot,
        commitment_inclusion_proofs: Vec<MerklePath<N::CommitmentsTreeParameters>>,
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
            if !commitment_inclusion_proof.verify(&commitments_root, commitment)? {
                return Err(anyhow!(
                    "Commitment {} does not correspond to root {}",
                    commitment,
                    commitments_root
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

        // Ensure the header inclusion proof is valid.
        if !header_inclusion_proof.verify(&header_root, &commitments_root)? {
            return Err(anyhow!(
                "Commitments root {} does not correspond to header root {}",
                commitments_root,
                header_root
            ));
        }

        // Ensure the block hash is valid.
        let candidate_block_hash =
            N::block_hash_crh().hash(&[previous_block_hash.to_bytes_le()?, header_root.to_bytes_le()?].concat())?;
        if candidate_block_hash != block_hash {
            return Err(anyhow!(
                "Candidate block hash {} does not match given block hash {}",
                candidate_block_hash,
                block_hash
            ));
        }

        Ok(Self {
            block_hash,
            previous_block_hash,
            header_root,
            header_inclusion_proof,
            commitments_root,
            commitment_inclusion_proofs,
            commitments,
        })
    }

    /// Returns the block hash used to prove inclusion of ledger-consumed records.
    pub fn block_hash(&self) -> N::BlockHash {
        self.block_hash
    }

    /// Returns the previous block hash.
    pub fn previous_block_hash(&self) -> N::BlockHash {
        self.previous_block_hash
    }

    /// Returns the block header root.
    pub fn header_root(&self) -> N::BlockHeaderRoot {
        self.header_root
    }

    /// Returns the block header inclusion proof.
    pub fn header_inclusion_proof(&self) -> &MerklePath<N::BlockHeaderTreeParameters> {
        &self.header_inclusion_proof
    }

    /// Returns the commitments root.
    pub fn commitments_root(&self) -> N::CommitmentsRoot {
        self.commitments_root
    }

    /// Returns a reference to the commitment inclusion proofs.
    pub fn commitment_inclusion_proofs(&self) -> &Vec<MerklePath<N::CommitmentsTreeParameters>> {
        &self.commitment_inclusion_proofs
    }
}

impl<N: Network> FromBytes for LedgerProof<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let block_hash = FromBytes::read_le(&mut reader)?;
        let previous_block_hash = FromBytes::read_le(&mut reader)?;
        let header_root = FromBytes::read_le(&mut reader)?;
        let header_inclusion_proof = FromBytes::read_le(&mut reader)?;
        let commitments_root = FromBytes::read_le(&mut reader)?;

        let mut commitment_inclusion_proofs = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            commitment_inclusion_proofs.push(FromBytes::read_le(&mut reader)?);
        }

        let mut commitments = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            commitments.push(FromBytes::read_le(&mut reader)?);
        }

        Ok(Self::new(
            block_hash,
            previous_block_hash,
            header_root,
            header_inclusion_proof,
            commitments_root,
            commitment_inclusion_proofs,
            commitments,
        )
        .expect("Failed to deserialize a ledger inclusion proof"))
    }
}

impl<N: Network> ToBytes for LedgerProof<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.block_hash.write_le(&mut writer)?;
        self.previous_block_hash.write_le(&mut writer)?;
        self.header_root.write_le(&mut writer)?;
        self.header_inclusion_proof.write_le(&mut writer)?;
        self.commitments_root.write_le(&mut writer)?;
        self.commitment_inclusion_proofs.write_le(&mut writer)?;
        self.commitments.write_le(&mut writer)
    }
}

impl<N: Network> Default for LedgerProof<N> {
    fn default() -> Self {
        let empty_commitment = N::Commitment::default();

        let header_tree = MerkleTree::<N::BlockHeaderTreeParameters>::new(
            Arc::new(N::block_header_tree_parameters().clone()),
            &vec![empty_commitment; N::POSW_NUM_LEAVES],
        )
        .expect("Ledger proof failed to create default header tree");

        let previous_block_hash = N::BlockHash::default();
        let header_root = *header_tree.root();
        let header_inclusion_proof = header_tree
            .generate_proof(2, &empty_commitment)
            .expect("Ledger proof failed to create default header inclusion proof");

        let block_hash = N::block_hash_crh()
            .hash(
                &[
                    previous_block_hash
                        .to_bytes_le()
                        .expect("Ledger proof failed to convert previous block hash to bytes"),
                    header_root
                        .to_bytes_le()
                        .expect("Ledger proof failed to convert header root to bytes"),
                ]
                .concat(),
            )
            .expect("Ledger proof failed to compute block hash");

        Self {
            block_hash,
            previous_block_hash,
            header_root,
            header_inclusion_proof,
            commitments_root: Default::default(),
            commitment_inclusion_proofs: vec![MerklePath::default(); N::NUM_INPUT_RECORDS],
            commitments: vec![empty_commitment; N::NUM_INPUT_RECORDS],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[rustfmt::skip]
    fn ledger_proof_new_test<N: Network>() -> Result<()> {
        let ledger = Ledger::<N>::new()?;
        assert_eq!(ledger.latest_block_height(), 0);
        assert_eq!(ledger.latest_block_transactions()?.len(), 1);

        let expected_block = ledger.latest_block()?;
        let coinbase_transaction = expected_block.to_coinbase_transaction()?;
        let expected_commitments = coinbase_transaction.commitments();

        // Create a ledger proof for two commitments.
        let ledger_proof = ledger.to_ledger_inclusion_proof(&expected_commitments)?;
        assert_eq!(ledger_proof.block_hash, expected_block.block_hash());
        assert_eq!(ledger_proof.previous_block_hash, expected_block.previous_block_hash());
        assert_eq!(ledger_proof.header_root, expected_block.header().to_header_root()?);
        assert_eq!(ledger_proof.commitments_root, expected_block.header().commitments_root());
        assert!(ledger_proof.commitment_inclusion_proofs[0].verify(&ledger_proof.commitments_root, &expected_commitments[0])?);
        assert!(!ledger_proof.commitment_inclusion_proofs[0].verify(&ledger_proof.commitments_root, &expected_commitments[1])?);
        assert!(!ledger_proof.commitment_inclusion_proofs[1].verify(&ledger_proof.commitments_root, &expected_commitments[0])?);
        assert!(ledger_proof.commitment_inclusion_proofs[1].verify(&ledger_proof.commitments_root, &expected_commitments[1])?);
        assert_eq!(ledger_proof.commitments, expected_commitments);

        // Create a ledger proof for one commitment and one noop.
        let ledger_proof = ledger.to_ledger_inclusion_proof(&[expected_commitments[0]])?;
        assert_eq!(ledger_proof.block_hash, expected_block.block_hash());
        assert_eq!(ledger_proof.previous_block_hash, expected_block.previous_block_hash());
        assert_eq!(ledger_proof.header_root, expected_block.header().to_header_root()?);
        assert_eq!(ledger_proof.commitments_root, expected_block.header().commitments_root());
        assert!(ledger_proof.commitment_inclusion_proofs[0].verify(&ledger_proof.commitments_root, &expected_commitments[0])?);
        assert!(!ledger_proof.commitment_inclusion_proofs[0].verify(&ledger_proof.commitments_root, &expected_commitments[1])?);
        assert!(!ledger_proof.commitment_inclusion_proofs[1].verify(&ledger_proof.commitments_root, &expected_commitments[0])?);
        assert!(!ledger_proof.commitment_inclusion_proofs[1].verify(&ledger_proof.commitments_root, &expected_commitments[1])?);
        assert_eq!(ledger_proof.commitments[0], expected_commitments[0]);
        assert_eq!(ledger_proof.commitments[1], Default::default());

        // Create a ledger proof for two noops.
        let ledger_proof = ledger.to_ledger_inclusion_proof(&[])?;
        assert_eq!(ledger_proof.block_hash, expected_block.block_hash());
        assert_eq!(ledger_proof.previous_block_hash, expected_block.previous_block_hash());
        assert_eq!(ledger_proof.header_root, expected_block.header().to_header_root()?);
        assert_eq!(ledger_proof.commitments_root, expected_block.header().commitments_root());
        assert!(!ledger_proof.commitment_inclusion_proofs[0].verify(&ledger_proof.commitments_root, &expected_commitments[0])?);
        assert!(!ledger_proof.commitment_inclusion_proofs[0].verify(&ledger_proof.commitments_root, &expected_commitments[1])?);
        assert!(!ledger_proof.commitment_inclusion_proofs[1].verify(&ledger_proof.commitments_root, &expected_commitments[0])?);
        assert!(!ledger_proof.commitment_inclusion_proofs[1].verify(&ledger_proof.commitments_root, &expected_commitments[1])?);
        assert_eq!(ledger_proof.commitments[0], Default::default());
        assert_eq!(ledger_proof.commitments[1], Default::default());

        Ok(())
    }

    #[test]
    fn test_new() {
        ledger_proof_new_test::<crate::testnet1::Testnet1>().unwrap();
        ledger_proof_new_test::<crate::testnet2::Testnet2>().unwrap();
    }
}
