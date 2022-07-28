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
use snarkvm_algorithms::merkle_tree::MerklePath;
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::{anyhow, Result};
use std::io::{Read, Result as IoResult, Write};

/// A ledger proof of inclusion.
#[derive(Clone, Debug)]
pub struct LedgerProof<N: Network> {
    ledger_root: N::LedgerRoot,
    ledger_root_inclusion_proof: MerklePath<N::LedgerRootParameters>,
    record_proof: RecordProof<N>,
}

impl<N: Network> LedgerProof<N> {
    ///
    /// Initializes a new ledger instance of `LedgerProof`.
    ///
    pub fn new(
        ledger_root: N::LedgerRoot,
        ledger_root_inclusion_proof: MerklePath<N::LedgerRootParameters>,
        record_proof: RecordProof<N>,
    ) -> Result<Self> {
        // Ensure the ledger root inclusion proof is valid.
        if !ledger_root_inclusion_proof.verify(&ledger_root, &record_proof.block_hash())? {
            return Err(anyhow!(
                "Block hash {} does not belong to ledger root {}",
                record_proof.block_hash(),
                ledger_root
            ));
        }

        Ok(Self { ledger_root, ledger_root_inclusion_proof, record_proof })
    }

    /// Create a new dummy ledger proof.
    pub fn new_dummy(local_proof: LocalProof<N>) -> Result<Self> {
        Ok(Self { record_proof: RecordProof::new_dummy(local_proof)?, ..Default::default() })
    }

    /// Returns the ledger root used to prove inclusion of ledger-consumed records.
    pub fn ledger_root(&self) -> N::LedgerRoot {
        self.ledger_root
    }

    /// Returns the ledger root inclusion proof.
    pub fn ledger_root_inclusion_proof(&self) -> &MerklePath<N::LedgerRootParameters> {
        &self.ledger_root_inclusion_proof
    }

    /// Returns the block hash.
    pub fn block_hash(&self) -> N::BlockHash {
        self.record_proof.block_hash()
    }

    /// Returns the previous block hash.
    pub fn previous_block_hash(&self) -> N::BlockHash {
        self.record_proof.previous_block_hash()
    }

    /// Returns the block header root.
    pub fn block_header_root(&self) -> N::BlockHeaderRoot {
        self.record_proof.block_header_root()
    }

    /// Returns the block header inclusion proof.
    pub fn block_header_inclusion_proof(&self) -> &MerklePath<N::BlockHeaderRootParameters> {
        self.record_proof.block_header_inclusion_proof()
    }

    /// Returns the transactions root.
    pub fn transactions_root(&self) -> N::TransactionsRoot {
        self.record_proof.transactions_root()
    }

    /// Returns the transactions inclusion proof.
    pub fn transactions_inclusion_proof(&self) -> &MerklePath<N::TransactionsRootParameters> {
        self.record_proof.transactions_inclusion_proof()
    }

    /// Returns the transaction ID.
    pub fn transaction_id(&self) -> N::TransactionID {
        self.record_proof.transaction_id()
    }

    /// Returns the transaction inclusion proof.
    pub fn transaction_inclusion_proof(&self) -> &MerklePath<N::TransactionIDParameters> {
        self.record_proof.transaction_inclusion_proof()
    }

    /// Returns the transition ID.
    pub fn transition_id(&self) -> N::TransitionID {
        self.record_proof.transition_id()
    }

    /// Returns the transition inclusion proof.
    pub fn transition_inclusion_proof(&self) -> &MerklePath<N::TransitionIDParameters> {
        self.record_proof.transition_inclusion_proof()
    }

    /// Returns the commitment.
    pub fn commitment(&self) -> N::Commitment {
        self.record_proof.commitment()
    }

    /// Returns the local proof.
    pub fn local_proof(&self) -> &LocalProof<N> {
        self.record_proof.local_proof()
    }
}

impl<N: Network> FromBytes for LedgerProof<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let ledger_root = FromBytes::read_le(&mut reader)?;
        let ledger_root_inclusion_proof = FromBytes::read_le(&mut reader)?;
        let record_proof = FromBytes::read_le(&mut reader)?;

        Ok(Self::new(ledger_root, ledger_root_inclusion_proof, record_proof)
            .expect("Failed to deserialize a ledger inclusion proof"))
    }
}

impl<N: Network> ToBytes for LedgerProof<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.ledger_root.write_le(&mut writer)?;
        self.ledger_root_inclusion_proof.write_le(&mut writer)?;
        self.record_proof.write_le(&mut writer)
    }
}

impl<N: Network> Default for LedgerProof<N> {
    fn default() -> Self {
        Self {
            ledger_root: LedgerTree::<N>::new().expect("Failed to create ledger tree").root(),
            ledger_root_inclusion_proof: MerklePath::default(),
            record_proof: Default::default(),
        }
    }
}
