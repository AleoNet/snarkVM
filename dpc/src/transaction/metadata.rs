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

use crate::Network;
use snarkvm_utilities::{FromBytes, ToBytes};

use std::io::{Read, Result as IoResult, Write};

/// The transaction metadata contains information relevant
/// for verifying the validity of the transaction.
#[derive(Derivative)]
#[derivative(
    Clone(bound = "N: Network"),
    Debug(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network")
)]
pub struct TransactionMetadata<N: Network> {
    block_hash: N::BlockHash,
    /// The root of the ledger commitment tree.
    ledger_digest: N::CommitmentsRoot,
    /// The ID of the inner circuit used to execute this transaction.
    inner_circuit_id: N::InnerCircuitID,
}

impl<N: Network> TransactionMetadata<N> {
    /// Initializes a new instance of transaction metadata.
    #[inline]
    pub fn new(
        block_hash: N::BlockHash,
        ledger_digest: N::CommitmentsRoot,
        inner_circuit_id: N::InnerCircuitID,
    ) -> Self {
        Self {
            block_hash,
            ledger_digest,
            inner_circuit_id,
        }
    }

    /// Returns the block hash.
    #[inline]
    pub fn block_hash(&self) -> N::BlockHash {
        self.block_hash
    }

    /// Returns a reference to the ledger digest.
    #[inline]
    pub fn ledger_digest(&self) -> &N::CommitmentsRoot {
        &self.ledger_digest
    }

    /// Returns a reference to the inner circuit ID.
    #[inline]
    pub fn inner_circuit_id(&self) -> &N::InnerCircuitID {
        &self.inner_circuit_id
    }
}

impl<N: Network> ToBytes for TransactionMetadata<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.block_hash.write_le(&mut writer)?;
        self.ledger_digest.write_le(&mut writer)?;
        self.inner_circuit_id.write_le(&mut writer)
    }
}

impl<N: Network> FromBytes for TransactionMetadata<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let block_hash = FromBytes::read_le(&mut reader)?;
        let ledger_digest = FromBytes::read_le(&mut reader)?;
        let inner_circuit_id = FromBytes::read_le(&mut reader)?;

        Ok(Self::new(block_hash, ledger_digest, inner_circuit_id))
    }
}
