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

use crate::{AleoAmount, Memo, Network, TransactionKernel};
use snarkvm_algorithms::{merkle_tree::MerkleTreeDigest, CommitmentScheme};
use snarkvm_fields::{ConstraintFieldError, ToConstraintField};

use anyhow::Result;

#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"))]
pub struct InnerPublicVariables<N: Network> {
    /// Transaction kernel
    pub(super) kernel: TransactionKernel<N>,
    /// Ledger digest
    pub(super) ledger_digest: MerkleTreeDigest<N::CommitmentsTreeParameters>,
    /// Output encrypted record hashes
    pub(super) encrypted_record_hashes: Vec<N::EncryptedRecordID>,

    // These are required in natively verifying an inner circuit proof.
    // However for verification in the outer circuit, these must be provided as witness.
    /// Program commitment
    pub(super) program_commitment: Option<<N::ProgramCommitmentScheme as CommitmentScheme>::Output>,
    /// Local data root
    pub(super) local_data_root: Option<N::LocalDataRoot>,
}

impl<N: Network> InnerPublicVariables<N> {
    pub fn blank() -> Self {
        Self {
            kernel: TransactionKernel::new(
                vec![N::SerialNumber::default(); N::NUM_INPUT_RECORDS],
                vec![N::Commitment::default(); N::NUM_OUTPUT_RECORDS],
                AleoAmount::ZERO,
                Memo::default(),
            )
            .expect("Failed to instantiate a blank transaction kernel"),
            ledger_digest: MerkleTreeDigest::<N::CommitmentsTreeParameters>::default(),
            encrypted_record_hashes: vec![N::EncryptedRecordID::default(); N::NUM_OUTPUT_RECORDS],
            program_commitment: Some(N::ProgramCommitment::default()),
            local_data_root: Some(N::LocalDataRoot::default()),
        }
    }

    pub fn new(
        kernel: &TransactionKernel<N>,
        ledger_digest: &MerkleTreeDigest<N::CommitmentsTreeParameters>,
        encrypted_record_hashes: &Vec<N::EncryptedRecordID>,
        program_commitment: Option<<N::ProgramCommitmentScheme as CommitmentScheme>::Output>,
        local_data_root: Option<N::LocalDataRoot>,
    ) -> Result<Self> {
        assert!(kernel.is_valid());
        assert_eq!(N::NUM_OUTPUT_RECORDS, encrypted_record_hashes.len());

        Ok(Self {
            kernel: kernel.clone(),
            ledger_digest: ledger_digest.clone(),
            encrypted_record_hashes: encrypted_record_hashes.clone(),
            program_commitment,
            local_data_root,
        })
    }
}

impl<N: Network> ToConstraintField<N::InnerScalarField> for InnerPublicVariables<N>
where
    MerkleTreeDigest<N::CommitmentsTreeParameters>: ToConstraintField<N::InnerScalarField>,
{
    fn to_field_elements(&self) -> Result<Vec<N::InnerScalarField>, ConstraintFieldError> {
        let mut v = Vec::new();
        v.extend_from_slice(&self.ledger_digest.to_field_elements()?);

        for serial_number in self.kernel.serial_numbers().iter().take(N::NUM_INPUT_RECORDS) {
            v.extend_from_slice(&ToConstraintField::<N::InnerScalarField>::to_field_elements(
                serial_number,
            )?);
        }

        for (cm, encrypted_record_hash) in self
            .kernel
            .commitments()
            .iter()
            .zip(&self.encrypted_record_hashes)
            .take(N::NUM_OUTPUT_RECORDS)
        {
            v.extend_from_slice(&cm.to_field_elements()?);
            v.extend_from_slice(&encrypted_record_hash.to_field_elements()?);
        }

        if let Some(program_commitment) = &self.program_commitment {
            v.extend_from_slice(&program_commitment.to_field_elements()?);
        }

        v.extend_from_slice(&self.kernel.memo().to_field_elements()?);
        v.extend_from_slice(&self.kernel.network_id().to_le_bytes().to_field_elements()?);

        if let Some(local_data_root) = &self.local_data_root {
            v.extend_from_slice(&local_data_root.to_field_elements()?);
        }

        v.extend_from_slice(&ToConstraintField::<N::InnerScalarField>::to_field_elements(
            &self.kernel.value_balance().0.to_le_bytes()[..],
        )?);
        Ok(v)
    }
}
