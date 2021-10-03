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
use snarkvm_algorithms::merkle_tree::MerkleTreeDigest;
use snarkvm_fields::{ConstraintFieldError, ToConstraintField};
use snarkvm_utilities::ToBytes;

use anyhow::Result;

#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"))]
pub struct InnerPublicVariables<N: Network> {
    /// Transaction ID
    pub(super) transaction_id: N::TransactionID,
    /// Ledger digest
    pub(super) ledger_digest: MerkleTreeDigest<N::CommitmentsTreeParameters>,
    /// Output encrypted record hashes
    pub(super) encrypted_record_ids: Vec<N::EncryptedRecordID>,

    // These are required in natively verifying an inner circuit proof.
    // However for verification in the outer circuit, these must be provided as witness.
    /// Program ID
    pub(super) program_id: Option<N::ProgramID>,
}

impl<N: Network> InnerPublicVariables<N> {
    pub fn blank() -> Self {
        Self {
            transaction_id: Default::default(),
            ledger_digest: MerkleTreeDigest::<N::CommitmentsTreeParameters>::default(),
            encrypted_record_ids: vec![N::EncryptedRecordID::default(); N::NUM_OUTPUT_RECORDS],
            program_id: Some(N::ProgramID::default()),
        }
    }

    pub fn new(
        transaction_id: N::TransactionID,
        ledger_digest: &MerkleTreeDigest<N::CommitmentsTreeParameters>,
        encrypted_record_ids: &Vec<N::EncryptedRecordID>,
        program_id: Option<N::ProgramID>,
    ) -> Result<Self> {
        assert_eq!(N::NUM_OUTPUT_RECORDS, encrypted_record_ids.len());

        Ok(Self {
            transaction_id,
            ledger_digest: ledger_digest.clone(),
            encrypted_record_ids: encrypted_record_ids.clone(),
            program_id,
        })
    }

    /// Returns the transaction ID.
    pub fn transaction_id(&self) -> N::TransactionID {
        self.transaction_id
    }
}

impl<N: Network> ToConstraintField<N::InnerScalarField> for InnerPublicVariables<N>
where
    MerkleTreeDigest<N::CommitmentsTreeParameters>: ToConstraintField<N::InnerScalarField>,
{
    fn to_field_elements(&self) -> Result<Vec<N::InnerScalarField>, ConstraintFieldError> {
        let mut v = Vec::new();
        v.extend_from_slice(&self.ledger_digest.to_field_elements()?);

        for encrypted_record_id in self.encrypted_record_ids.iter().take(N::NUM_OUTPUT_RECORDS) {
            v.extend_from_slice(&encrypted_record_id.to_field_elements()?);
        }

        if let Some(program_id) = &self.program_id {
            v.extend_from_slice(&program_id.to_bytes_le()?.to_field_elements()?);
        }

        v.extend_from_slice(&self.transaction_id.to_field_elements()?);

        Ok(v)
    }
}
