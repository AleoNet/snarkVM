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

use crate::{
    testnet1::{outer_circuit_gadget::execute_outer_circuit, program::Execution, Testnet1Components, Transaction},
    AleoAmount,
    TransactionScheme,
};
use snarkvm_algorithms::{
    merkle_tree::MerkleTreeDigest,
    traits::{CommitmentScheme, MerkleParameters, SignatureScheme, CRH, SNARK},
};
use snarkvm_fields::ToConstraintField;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSynthesizer, ConstraintSystem};

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Testnet1Components"))]
pub struct OuterCircuit<C: Testnet1Components> {
    // Inner snark verifier public inputs
    ledger_digest: MerkleTreeDigest<C::RecordCommitmentTreeParameters>,
    old_serial_numbers: Vec<<C::AccountSignature as SignatureScheme>::PublicKey>,
    new_commitments: Vec<C::RecordCommitment>,
    new_encrypted_record_hashes: Vec<C::EncryptedRecordDigest>,
    memo: <Transaction<C> as TransactionScheme>::Memorandum,
    value_balance: AleoAmount,
    network_id: u8,

    // Inner snark verifier private inputs
    inner_snark_vk: <C::InnerSNARK as SNARK>::VerifyingKey,
    inner_snark_proof: <C::InnerSNARK as SNARK>::Proof,

    program_proofs: Vec<Execution>,
    program_commitment: <C::ProgramCommitmentScheme as CommitmentScheme>::Output,
    program_randomness: <C::ProgramCommitmentScheme as CommitmentScheme>::Randomness,
    local_data_root: C::LocalDataDigest,

    inner_circuit_id: <C::InnerCircuitIDCRH as CRH>::Output,
}

impl<C: Testnet1Components> OuterCircuit<C> {
    pub fn blank(
        inner_snark_vk: <C::InnerSNARK as SNARK>::VerifyingKey,
        inner_snark_proof: <C::InnerSNARK as SNARK>::Proof,
        program_snark_vk_and_proof: Execution,
    ) -> Self {
        let ledger_digest = MerkleTreeDigest::<C::RecordCommitmentTreeParameters>::default();
        let old_serial_numbers =
            vec![<C::AccountSignature as SignatureScheme>::PublicKey::default(); C::NUM_INPUT_RECORDS];
        let new_commitments = vec![C::RecordCommitment::default(); C::NUM_OUTPUT_RECORDS];
        let new_encrypted_record_hashes = vec![C::EncryptedRecordDigest::default(); C::NUM_OUTPUT_RECORDS];
        let memo = [0u8; 64];
        let value_balance = AleoAmount::ZERO;
        let network_id = C::NETWORK_ID;

        let program_proofs = vec![program_snark_vk_and_proof.clone(); C::NUM_TOTAL_RECORDS];
        let program_commitment = <C::ProgramCommitmentScheme as CommitmentScheme>::Output::default();
        let program_randomness = <C::ProgramCommitmentScheme as CommitmentScheme>::Randomness::default();
        let local_data_root = C::LocalDataDigest::default();

        let inner_circuit_id = <C::InnerCircuitIDCRH as CRH>::Output::default();

        Self {
            ledger_digest,
            old_serial_numbers,
            new_commitments,
            memo,
            new_encrypted_record_hashes,
            value_balance,
            network_id,
            inner_snark_vk,
            inner_snark_proof,
            program_proofs,
            program_commitment,
            program_randomness,
            local_data_root,
            inner_circuit_id,
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub fn new(
        // Inner SNARK public inputs
        ledger_digest: MerkleTreeDigest<C::RecordCommitmentTreeParameters>,
        old_serial_numbers: Vec<<C::AccountSignature as SignatureScheme>::PublicKey>,
        new_commitments: Vec<C::RecordCommitment>,
        new_encrypted_record_hashes: Vec<C::EncryptedRecordDigest>,
        memo: <Transaction<C> as TransactionScheme>::Memorandum,
        value_balance: AleoAmount,
        network_id: u8,

        // Inner SNARK private inputs
        inner_snark_vk: <C::InnerSNARK as SNARK>::VerifyingKey,
        inner_snark_proof: <C::InnerSNARK as SNARK>::Proof,

        // Private program input = Verification key and input
        // Commitment contains commitment to hash of death program vk.
        program_proofs: Vec<Execution>,
        program_commitment: <C::ProgramCommitmentScheme as CommitmentScheme>::Output,
        program_randomness: <C::ProgramCommitmentScheme as CommitmentScheme>::Randomness,
        local_data_root: C::LocalDataDigest,

        // Inner circuit ID
        inner_circuit_id: <C::InnerCircuitIDCRH as CRH>::Output,
    ) -> Self {
        assert_eq!(C::NUM_TOTAL_RECORDS, program_proofs.len());
        assert_eq!(C::NUM_OUTPUT_RECORDS, new_commitments.len());
        assert_eq!(C::NUM_OUTPUT_RECORDS, new_encrypted_record_hashes.len());

        Self {
            ledger_digest,
            old_serial_numbers,
            new_commitments,
            new_encrypted_record_hashes,
            memo,
            value_balance,
            network_id,
            inner_snark_vk,
            inner_snark_proof,
            program_proofs,
            program_commitment,
            program_randomness,
            local_data_root,
            inner_circuit_id,
        }
    }
}

impl<C: Testnet1Components> ConstraintSynthesizer<C::OuterScalarField> for OuterCircuit<C>
where
    <C::AccountCommitmentScheme as CommitmentScheme>::Output: ToConstraintField<C::InnerScalarField>,
    <C::ProgramCommitmentScheme as CommitmentScheme>::Output: ToConstraintField<C::InnerScalarField>,
    <C::RecordCommitmentTreeParameters as MerkleParameters>::H: ToConstraintField<C::InnerScalarField>,
    MerkleTreeDigest<C::RecordCommitmentTreeParameters>: ToConstraintField<C::InnerScalarField>,
{
    fn generate_constraints<CS: ConstraintSystem<C::OuterScalarField>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        execute_outer_circuit::<C, CS>(
            cs,
            &self.ledger_digest,
            &self.old_serial_numbers,
            &self.new_commitments,
            &self.new_encrypted_record_hashes,
            &self.memo,
            self.value_balance,
            self.network_id,
            &self.inner_snark_vk,
            &self.inner_snark_proof,
            &self.program_proofs,
            &self.program_commitment,
            &self.program_randomness,
            &self.local_data_root,
            &self.inner_circuit_id,
        )?;
        Ok(())
    }
}
