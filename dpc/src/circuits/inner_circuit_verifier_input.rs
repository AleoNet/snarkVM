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

use crate::{AleoAmount, Parameters};
use snarkvm_algorithms::{
    merkle_tree::MerkleTreeDigest,
    traits::{CommitmentScheme, MerkleParameters, SignatureScheme, CRH},
};
use snarkvm_fields::{ConstraintFieldError, ToConstraintField};

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"))]
pub struct InnerCircuitVerifierInput<C: Parameters> {
    // Ledger digest
    pub ledger_digest: MerkleTreeDigest<C::RecordCommitmentTreeParameters>,

    // Input record serial numbers
    pub old_serial_numbers: Vec<<C::AccountSignatureScheme as SignatureScheme>::PublicKey>,

    // Output record commitments
    pub new_commitments: Vec<C::RecordCommitment>,

    // New encrypted record hashes
    pub new_encrypted_record_hashes: Vec<C::EncryptedRecordDigest>,

    // Program input commitment and local data root.
    // These are required in natively verifying an inner circuit proof.
    // However for verification in the outer circuit, these must be provided as witness.
    pub program_commitment: Option<<C::ProgramCommitmentScheme as CommitmentScheme>::Output>,
    pub local_data_root: Option<C::LocalDataDigest>,

    pub memo: [u8; 64],
    pub value_balance: AleoAmount,
    pub network_id: u8,
}

impl<C: Parameters> ToConstraintField<C::InnerScalarField> for InnerCircuitVerifierInput<C>
where
    <C::AccountCommitmentScheme as CommitmentScheme>::Output: ToConstraintField<C::InnerScalarField>,
    <<C::RecordCommitmentTreeParameters as MerkleParameters>::H as CRH>::Parameters:
        ToConstraintField<C::InnerScalarField>,
    MerkleTreeDigest<C::RecordCommitmentTreeParameters>: ToConstraintField<C::InnerScalarField>,
{
    fn to_field_elements(&self) -> Result<Vec<C::InnerScalarField>, ConstraintFieldError> {
        let mut v = Vec::new();
        v.extend_from_slice(&C::account_commitment_scheme().to_field_elements()?);
        v.extend_from_slice(&C::account_encryption_scheme().to_field_elements()?);
        v.extend_from_slice(&C::account_signature_scheme().to_field_elements()?);
        v.extend_from_slice(&C::record_commitment_scheme().to_field_elements()?);
        v.extend_from_slice(&C::encrypted_record_crh().to_field_elements()?);
        v.extend_from_slice(&C::program_commitment_scheme().to_field_elements()?);
        v.extend_from_slice(&C::local_data_crh().to_field_elements()?);
        v.extend_from_slice(&C::local_data_commitment_scheme().to_field_elements()?);
        v.extend_from_slice(&C::serial_number_nonce_crh().to_field_elements()?);
        v.extend_from_slice(
            &C::record_commitment_tree_parameters()
                .crh()
                .parameters()
                .to_field_elements()?,
        );

        v.extend_from_slice(&self.ledger_digest.to_field_elements()?);

        for sn in &self.old_serial_numbers {
            v.extend_from_slice(&sn.to_field_elements()?);
        }

        for (cm, encrypted_record_hash) in self.new_commitments.iter().zip(&self.new_encrypted_record_hashes) {
            v.extend_from_slice(&cm.to_field_elements()?);
            v.extend_from_slice(&encrypted_record_hash.to_field_elements()?);
        }

        if let Some(program_commitment) = &self.program_commitment {
            v.extend_from_slice(&program_commitment.to_field_elements()?);
        }

        v.extend_from_slice(&ToConstraintField::<C::InnerScalarField>::to_field_elements(
            &self.memo,
        )?);
        v.extend_from_slice(&ToConstraintField::<C::InnerScalarField>::to_field_elements(
            &[self.network_id][..],
        )?);

        if let Some(local_data_root) = &self.local_data_root {
            v.extend_from_slice(&local_data_root.to_field_elements()?);
        }

        v.extend_from_slice(&ToConstraintField::<C::InnerScalarField>::to_field_elements(
            &self.value_balance.0.to_le_bytes()[..],
        )?);
        Ok(v)
    }
}
