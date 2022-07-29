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
use snarkvm_algorithms::{merkle_tree::MerklePath, prelude::*};
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use anyhow::{anyhow, Result};
use std::io::{Read, Result as IoResult, Write};

/// A proof of inclusion for a record in a block.
#[derive(Clone, Debug)]
pub struct RecordProof<N: Network> {
    block_hash: N::BlockHash,
    previous_block_hash: N::BlockHash,
    block_header_root: N::BlockHeaderRoot,
    block_header_inclusion_proof: MerklePath<N::BlockHeaderRootParameters>,
    transactions_root: N::TransactionsRoot,
    transactions_inclusion_proof: MerklePath<N::TransactionsRootParameters>,
    local_proof: LocalProof<N>,
}

impl<N: Network> RecordProof<N> {
    ///
    /// Initializes a new dummy instance of `RecordProof`.
    ///
    pub fn new_dummy(local_proof: LocalProof<N>) -> Result<Self> {
        Ok(Self { local_proof, ..Default::default() })
    }

    ///
    /// Initializes a new instance of `RecordProof`.
    ///
    pub fn new(
        block_hash: N::BlockHash,
        previous_block_hash: N::BlockHash,
        block_header_root: N::BlockHeaderRoot,
        block_header_inclusion_proof: MerklePath<N::BlockHeaderRootParameters>,
        transactions_root: N::TransactionsRoot,
        transactions_inclusion_proof: MerklePath<N::TransactionsRootParameters>,
        local_proof: LocalProof<N>,
    ) -> Result<Self> {
        // Ensure the transactions inclusion proof is valid.
        let transaction_id = local_proof.transaction_id();
        if !transactions_inclusion_proof.verify(&transactions_root, &transaction_id)? {
            return Err(anyhow!(
                "Transaction {} does not belong to transactions root {}",
                transaction_id,
                transactions_root
            ));
        }

        // Ensure the block header inclusion proof is valid.
        if !block_header_inclusion_proof.verify(&block_header_root, &transactions_root)? {
            return Err(anyhow!(
                "Transactions root {} does not belong to block header {}",
                transactions_root,
                block_header_root
            ));
        }

        // Ensure the block hash is valid.
        let candidate_block_hash: N::BlockHash =
            N::block_hash_crh().hash_bytes(&to_bytes_le![previous_block_hash, block_header_root]?)?.into();
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
            block_header_root,
            block_header_inclusion_proof,
            transactions_root,
            transactions_inclusion_proof,
            local_proof,
        })
    }

    /// Returns the block hash.
    pub fn block_hash(&self) -> N::BlockHash {
        self.block_hash
    }

    /// Returns the previous block hash.
    pub fn previous_block_hash(&self) -> N::BlockHash {
        self.previous_block_hash
    }

    /// Returns the block header root.
    pub fn block_header_root(&self) -> N::BlockHeaderRoot {
        self.block_header_root
    }

    /// Returns the block header inclusion proof.
    pub fn block_header_inclusion_proof(&self) -> &MerklePath<N::BlockHeaderRootParameters> {
        &self.block_header_inclusion_proof
    }

    /// Returns the transactions root.
    pub fn transactions_root(&self) -> N::TransactionsRoot {
        self.transactions_root
    }

    /// Returns the transactions inclusion proof.
    pub fn transactions_inclusion_proof(&self) -> &MerklePath<N::TransactionsRootParameters> {
        &self.transactions_inclusion_proof
    }

    /// Returns the transaction ID.
    pub fn transaction_id(&self) -> N::TransactionID {
        self.local_proof.transaction_id()
    }

    /// Returns the transaction inclusion proof.
    pub fn transaction_inclusion_proof(&self) -> &MerklePath<N::TransactionIDParameters> {
        self.local_proof.transaction_inclusion_proof()
    }

    /// Returns the transition ID.
    pub fn transition_id(&self) -> N::TransitionID {
        self.local_proof.transition_id()
    }

    /// Returns the transition inclusion proof.
    pub fn transition_inclusion_proof(&self) -> &MerklePath<N::TransitionIDParameters> {
        self.local_proof.transition_inclusion_proof()
    }

    /// Returns the commitment.
    pub fn commitment(&self) -> N::Commitment {
        self.local_proof.commitment()
    }

    /// Returns the local proof.
    pub fn local_proof(&self) -> &LocalProof<N> {
        &self.local_proof
    }
}

impl<N: Network> FromBytes for RecordProof<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let block_hash = FromBytes::read_le(&mut reader)?;
        let previous_block_hash = FromBytes::read_le(&mut reader)?;
        let block_header_root = FromBytes::read_le(&mut reader)?;
        let block_header_inclusion_proof = FromBytes::read_le(&mut reader)?;
        let transactions_root = FromBytes::read_le(&mut reader)?;
        let transactions_inclusion_proof = FromBytes::read_le(&mut reader)?;
        let local_proof = FromBytes::read_le(&mut reader)?;

        Ok(Self::new(
            block_hash,
            previous_block_hash,
            block_header_root,
            block_header_inclusion_proof,
            transactions_root,
            transactions_inclusion_proof,
            local_proof,
        )
        .expect("Failed to deserialize a record inclusion proof"))
    }
}

impl<N: Network> ToBytes for RecordProof<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.block_hash.write_le(&mut writer)?;
        self.previous_block_hash.write_le(&mut writer)?;
        self.block_header_root.write_le(&mut writer)?;
        self.block_header_inclusion_proof.write_le(&mut writer)?;
        self.transactions_root.write_le(&mut writer)?;
        self.transactions_inclusion_proof.write_le(&mut writer)?;
        self.local_proof.write_le(&mut writer)
    }
}

impl<N: Network> Default for RecordProof<N> {
    fn default() -> Self {
        Self {
            block_hash: Default::default(),
            previous_block_hash: Default::default(),
            block_header_root: Default::default(),
            block_header_inclusion_proof: MerklePath::default(),
            transactions_root: Default::default(),
            transactions_inclusion_proof: MerklePath::default(),
            local_proof: Default::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[rustfmt::skip]
    fn record_proof_new_test<N: Network>() -> Result<()> {
        let ledger = Ledger::<N>::new()?;
        assert_eq!(ledger.latest_block_height(), 0);
        assert_eq!(ledger.latest_block_transactions()?.len(), 1);

        let expected_block = ledger.latest_block()?;
        let coinbase_transaction = expected_block.to_coinbase_transaction()?;
        let expected_commitments = coinbase_transaction.commitments().collect::<Vec<_>>();

        // Create a ledger proof for one commitment.
        let record_proof = ledger.to_ledger_proof(*expected_commitments[0]).unwrap();
        assert_eq!(record_proof.block_hash(), expected_block.hash());
        assert_eq!(record_proof.previous_block_hash(), expected_block.previous_block_hash());
        assert_eq!(record_proof.block_header_root(), expected_block.header().to_header_root()?);
        // assert_eq!(record_proof.commitments_root(), expected_block.header().commitments_root());
        // assert!(record_proof.commitment_inclusion_proofs[0].verify(&record_proof.commitments_root, &expected_commitments[0])?);
        // assert!(!record_proof.commitment_inclusion_proofs[0].verify(&record_proof.commitments_root, &expected_commitments[1])?);
        // assert!(!record_proof.commitment_inclusion_proofs[1].verify(&record_proof.commitments_root, &expected_commitments[0])?);
        // assert!(!record_proof.commitment_inclusion_proofs[1].verify(&record_proof.commitments_root, &expected_commitments[1])?);
        // assert_eq!(record_proof.commitments[0], expected_commitments[0]);
        // assert_eq!(record_proof.commitments[1], Default::default());

        Ok(())
    }

    #[test]
    fn test_new() {
        record_proof_new_test::<crate::testnet1::Testnet1>().unwrap();
        record_proof_new_test::<crate::testnet2::Testnet2>().unwrap();
    }
}
