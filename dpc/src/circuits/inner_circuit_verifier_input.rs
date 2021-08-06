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

use crate::{Parameters, TransactionKernel};
use snarkvm_algorithms::{merkle_tree::MerkleTreeDigest, traits::CommitmentScheme};
use snarkvm_fields::{ConstraintFieldError, ToConstraintField};

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"))]
pub struct InnerCircuitVerifierInput<C: Parameters> {
    // /// Network ID
    // pub network_id: u8,
    // /// Input record serial numbers
    // pub serial_numbers: Vec<<C::AccountSignatureScheme as SignatureScheme>::PublicKey>,
    // /// Output record commitments
    // pub commitments: Vec<C::RecordCommitment>,
    // /// Value balance
    // pub value_balance: AleoAmount,
    // /// Memo field
    // pub memo: [u8; 64],
    /// Transaction kernel
    pub kernel: TransactionKernel<C>,
    /// Ledger digest
    pub ledger_digest: MerkleTreeDigest<C::RecordCommitmentTreeParameters>,
    /// Output encrypted record hashes
    pub encrypted_record_hashes: Vec<C::EncryptedRecordDigest>,

    // These are required in natively verifying an inner circuit proof.
    // However for verification in the outer circuit, these must be provided as witness.
    /// Program commitment
    pub program_commitment: Option<<C::ProgramCommitmentScheme as CommitmentScheme>::Output>,
    /// Local data root
    pub local_data_root: Option<C::LocalDataRoot>,
}

impl<C: Parameters> ToConstraintField<C::InnerScalarField> for InnerCircuitVerifierInput<C>
where
    MerkleTreeDigest<C::RecordCommitmentTreeParameters>: ToConstraintField<C::InnerScalarField>,
{
    fn to_field_elements(&self) -> Result<Vec<C::InnerScalarField>, ConstraintFieldError> {
        let mut v = Vec::new();
        v.extend_from_slice(&self.ledger_digest.to_field_elements()?);

        for sn in &self.kernel.serial_numbers {
            v.extend_from_slice(&sn.to_field_elements()?);
        }

        for (cm, encrypted_record_hash) in self.kernel.commitments.iter().zip(&self.encrypted_record_hashes) {
            v.extend_from_slice(&cm.to_field_elements()?);
            v.extend_from_slice(&encrypted_record_hash.to_field_elements()?);
        }

        if let Some(program_commitment) = &self.program_commitment {
            v.extend_from_slice(&program_commitment.to_field_elements()?);
        }

        v.extend_from_slice(&ToConstraintField::<C::InnerScalarField>::to_field_elements(
            &self.kernel.memo,
        )?);
        v.extend_from_slice(&ToConstraintField::<C::InnerScalarField>::to_field_elements(
            &[self.kernel.network_id][..],
        )?);

        if let Some(local_data_root) = &self.local_data_root {
            v.extend_from_slice(&local_data_root.to_field_elements()?);
        }

        v.extend_from_slice(&ToConstraintField::<C::InnerScalarField>::to_field_elements(
            &self.kernel.value_balance.0.to_le_bytes()[..],
        )?);
        Ok(v)
    }
}
