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
use snarkvm_algorithms::{merkle_tree::MerklePath, prelude::*};
use snarkvm_utilities::ToBytes;

use anyhow::{anyhow, Result};
use itertools::Itertools;

#[allow(unused)]
/// A ledger proof of inclusion.
pub struct LedgerProof<N: Network> {
    block_hash: N::BlockHash,
    previous_block_hash: N::BlockHash,
    header_root: N::BlockHeaderRoot,
    header_inclusion_proof: MerklePath<N::BlockHeaderTreeParameters>,
    commitments_root: N::CommitmentsRoot,
    commitment_inclusion_proofs: Vec<MerklePath<N::CommitmentsTreeParameters>>,
    commitments: Vec<N::Commitment>,
}

impl<N: Network> LedgerProof<N> {
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
        if commitments.len() != N::NUM_INPUT_RECORDS {
            return Err(anyhow!(
                "Incorrect number of given commitments. Expected {}, found {}",
                N::NUM_INPUT_RECORDS,
                commitments.len(),
            ));
        }

        // Ensure the correct number of commitment inclusion proofs is given.
        if commitment_inclusion_proofs.len() != N::NUM_INPUT_RECORDS {
            return Err(anyhow!(
                "Incorrect number of given commitment inclusion proofs. Expected {}, found {}",
                N::NUM_INPUT_RECORDS,
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

    pub fn commitments_root(&self) -> N::CommitmentsRoot {
        self.commitments_root
    }

    pub fn commitment_inclusion_proofs(&self) -> Vec<MerklePath<N::CommitmentsTreeParameters>> {
        self.commitment_inclusion_proofs.clone()
    }
}

impl<N: Network> Default for LedgerProof<N> {
    fn default() -> Self {
        Self {
            block_hash: Default::default(),
            previous_block_hash: Default::default(),
            header_root: Default::default(),
            header_inclusion_proof: MerklePath::default(),
            commitments_root: Default::default(),
            commitment_inclusion_proofs: vec![MerklePath::default(); N::NUM_INPUT_RECORDS].into(),
            commitments: vec![Default::default(); N::NUM_INPUT_RECORDS],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ledger_proof_new_test<N: Network>() -> Result<()> {
        let ledger = Ledger::<N>::new()?;
        assert_eq!(ledger.latest_block_height(), 0);
        assert_eq!(ledger.latest_block_transactions()?.len(), 1);

        let block = ledger.latest_block()?;
        let coinbase_transaction = block.to_coinbase_transaction()?;
        let commitments = coinbase_transaction.commitments();
        assert!(ledger.to_ledger_inclusion_proof(commitments).is_ok());

        Ok(())
    }

    #[test]
    fn test_new() {
        ledger_proof_new_test::<crate::testnet1::Testnet1>().unwrap();
        ledger_proof_new_test::<crate::testnet2::Testnet2>().unwrap();
    }
}
