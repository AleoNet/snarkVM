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

use crate::base_dpc::{inner_circuit_verifier_input::InnerCircuitVerifierInput, BaseDPCComponents};
use snarkvm_algorithms::{
    merkle_tree::MerkleTreeDigest,
    traits::{CommitmentScheme, EncryptionScheme, MerkleParameters, SignatureScheme, CRH},
};
use snarkvm_curves::{errors::ConstraintFieldError, traits::to_field_vec::ToConstraintField};
use snarkvm_r1cs::errors::SynthesisError;

use snarkvm_utilities::{bytes::ToBytes, to_bytes};

#[derive(Derivative)]
#[derivative(Clone(bound = "C: BaseDPCComponents"))]
pub struct OuterCircuitVerifierInput<C: BaseDPCComponents> {
    pub inner_snark_verifier_input: InnerCircuitVerifierInput<C>,
    pub inner_snark_id: <C::InnerSNARKVerificationKeyCRH as CRH>::Output,
}

impl<C: BaseDPCComponents> ToConstraintField<C::OuterField> for OuterCircuitVerifierInput<C>
where
    <C::ProgramVerificationKeyCommitment as CommitmentScheme>::Parameters: ToConstraintField<C::OuterField>,
    <C::ProgramVerificationKeyCommitment as CommitmentScheme>::Output: ToConstraintField<C::OuterField>,
    <C::ProgramVerificationKeyCRH as CRH>::Parameters: ToConstraintField<C::OuterField>,

    <C::InnerSNARKVerificationKeyCRH as CRH>::Parameters: ToConstraintField<C::OuterField>,
    <C::InnerSNARKVerificationKeyCRH as CRH>::Output: ToConstraintField<C::OuterField>,

    <C::AccountCommitment as CommitmentScheme>::Parameters: ToConstraintField<C::InnerField>,
    <C::AccountCommitment as CommitmentScheme>::Output: ToConstraintField<C::InnerField>,

    <C::AccountEncryption as EncryptionScheme>::Parameters: ToConstraintField<C::InnerField>,

    <C::AccountSignature as SignatureScheme>::Parameters: ToConstraintField<C::InnerField>,
    <C::AccountSignature as SignatureScheme>::PublicKey: ToConstraintField<C::InnerField>,

    <C::RecordCommitment as CommitmentScheme>::Parameters: ToConstraintField<C::InnerField>,
    <C::RecordCommitment as CommitmentScheme>::Output: ToConstraintField<C::InnerField>,

    <C::EncryptedRecordCRH as CRH>::Parameters: ToConstraintField<C::InnerField>,
    <C::EncryptedRecordCRH as CRH>::Output: ToConstraintField<C::InnerField>,

    <C::SerialNumberNonceCRH as CRH>::Parameters: ToConstraintField<C::InnerField>,

    <C::ProgramVerificationKeyCommitment as CommitmentScheme>::Parameters: ToConstraintField<C::InnerField>,
    <C::ProgramVerificationKeyCommitment as CommitmentScheme>::Output: ToConstraintField<C::InnerField>,

    <C::LocalDataCRH as CRH>::Parameters: ToConstraintField<C::InnerField>,
    <C::LocalDataCRH as CRH>::Output: ToConstraintField<C::InnerField>,

    <<C::MerkleParameters as MerkleParameters>::H as CRH>::Parameters: ToConstraintField<C::InnerField>,
    MerkleTreeDigest<C::MerkleParameters>: ToConstraintField<C::InnerField>,
{
    fn to_field_elements(&self) -> Result<Vec<C::OuterField>, ConstraintFieldError> {
        let mut v = Vec::new();

        v.extend_from_slice(
            &self
                .inner_snark_verifier_input
                .system_parameters
                .program_verification_key_commitment
                .parameters()
                .to_field_elements()?,
        );
        v.extend_from_slice(
            &self
                .inner_snark_verifier_input
                .system_parameters
                .program_verification_key_crh
                .parameters()
                .to_field_elements()?,
        );
        v.extend_from_slice(
            &self
                .inner_snark_verifier_input
                .system_parameters
                .inner_snark_verification_key_crh
                .parameters()
                .to_field_elements()?,
        );
        // Convert inner snark verifier inputs into `OuterField` field elements

        let inner_snark_field_elements = &self.inner_snark_verifier_input.to_field_elements()?;

        for inner_snark_fe in inner_snark_field_elements {
            let inner_snark_fe_bytes = to_bytes![inner_snark_fe].map_err(|_| SynthesisError::AssignmentMissing)?;
            v.extend_from_slice(&ToConstraintField::<C::OuterField>::to_field_elements(
                inner_snark_fe_bytes.as_slice(),
            )?);
        }

        v.extend_from_slice(&self.inner_snark_verifier_input.program_commitment.to_field_elements()?);
        v.extend_from_slice(&self.inner_snark_id.to_field_elements()?);
        Ok(v)
    }
}
