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

use crate::Parameters;
use snarkvm_algorithms::merkle_tree::MerkleTreeDigest;
use snarkvm_utilities::{FromBytes, ToBytes};

use std::io::{Read, Result as IoResult, Write};

/// The transaction metadata contains information relevant
/// for verifying the validity of the transaction.
#[derive(Derivative)]
#[derivative(
    Clone(bound = "C: Parameters"),
    Debug(bound = "C: Parameters"),
    PartialEq(bound = "C: Parameters"),
    Eq(bound = "C: Parameters")
)]
pub struct TransactionMetadata<C: Parameters> {
    /// The root of the ledger commitment tree.
    ledger_digest: MerkleTreeDigest<C::LedgerCommitmentsTreeParameters>,
    /// The ID of the inner circuit used to execute this transaction.
    inner_circuit_id: C::InnerCircuitID,
}

impl<C: Parameters> TransactionMetadata<C> {
    /// Initializes a new instance of transaction metadata.
    #[inline]
    pub fn new(
        ledger_digest: MerkleTreeDigest<C::LedgerCommitmentsTreeParameters>,
        inner_circuit_id: C::InnerCircuitID,
    ) -> Self {
        Self {
            ledger_digest,
            inner_circuit_id,
        }
    }

    /// Returns a reference to the ledger digest.
    #[inline]
    pub fn ledger_digest(&self) -> &MerkleTreeDigest<C::LedgerCommitmentsTreeParameters> {
        &self.ledger_digest
    }

    /// Returns a reference to the inner circuit ID.
    #[inline]
    pub fn inner_circuit_id(&self) -> &C::InnerCircuitID {
        &self.inner_circuit_id
    }
}

impl<C: Parameters> ToBytes for TransactionMetadata<C> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.ledger_digest.write_le(&mut writer)?;
        self.inner_circuit_id.write_le(&mut writer)
    }
}

impl<C: Parameters> FromBytes for TransactionMetadata<C> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let ledger_digest = FromBytes::read_le(&mut reader)?;
        let inner_circuit_id = FromBytes::read_le(&mut reader)?;

        Ok(Self::new(ledger_digest, inner_circuit_id))
    }
}
