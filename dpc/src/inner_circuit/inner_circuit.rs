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
    encrypted::RecordEncryptionGadgetComponents,
    execute_inner_circuit,
    record::Record,
    AleoAmount,
    Parameters,
    PrivateKey,
};
use snarkvm_algorithms::{
    merkle_tree::{MerklePath, MerkleTreeDigest},
    traits::{CommitmentScheme, EncryptionScheme, SignatureScheme},
};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSynthesizer, ConstraintSystem};

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"))]
pub struct InnerCircuit<C: Parameters> {
    // Ledger
    ledger_digest: MerkleTreeDigest<C::RecordCommitmentTreeParameters>,

    // Inputs for old records.
    old_records: Vec<Record<C>>,
    old_witnesses: Vec<MerklePath<C::RecordCommitmentTreeParameters>>,
    old_private_keys: Vec<PrivateKey<C>>,
    old_serial_numbers: Vec<<C::AccountSignature as SignatureScheme>::PublicKey>,

    // Inputs for new records.
    new_records: Vec<Record<C>>,
    new_serial_number_nonce_randomness: Vec<[u8; 32]>,
    new_commitments: Vec<C::RecordCommitment>,

    // Inputs for encryption of new records.
    new_records_encryption_randomness: Vec<<C::AccountEncryption as EncryptionScheme>::Randomness>,
    new_records_encryption_gadget_components: Vec<RecordEncryptionGadgetComponents<C>>,
    new_encrypted_record_hashes: Vec<C::EncryptedRecordDigest>,

    // Commitment to Programs and to local data.
    program_commitment: <C::ProgramCommitmentScheme as CommitmentScheme>::Output,
    program_randomness: <C::ProgramCommitmentScheme as CommitmentScheme>::Randomness,

    local_data_root: C::LocalDataDigest,
    local_data_commitment_randomizers: Vec<<C::LocalDataCommitmentScheme as CommitmentScheme>::Randomness>,

    memo: [u8; 64],
    value_balance: AleoAmount,
    network_id: u8,
}

impl<C: Parameters> InnerCircuit<C> {
    pub fn blank() -> Self {
        let num_input_records = C::NUM_INPUT_RECORDS;
        let num_output_records = C::NUM_OUTPUT_RECORDS;
        let digest = MerkleTreeDigest::<C::RecordCommitmentTreeParameters>::default();

        let old_serial_numbers =
            vec![<C::AccountSignature as SignatureScheme>::PublicKey::default(); num_input_records];
        let old_records = vec![Record::default(); num_input_records];
        let old_witnesses = vec![MerklePath::default(); num_input_records];
        let old_private_keys = vec![PrivateKey::default(); num_input_records];

        let new_commitments = vec![C::RecordCommitment::default(); num_output_records];
        let new_serial_number_nonce_randomness = vec![[0u8; 32]; num_output_records];
        let new_records = vec![Record::default(); num_output_records];

        let new_records_encryption_randomness =
            vec![<C::AccountEncryption as EncryptionScheme>::Randomness::default(); num_output_records];

        let new_records_encryption_gadget_components =
            vec![RecordEncryptionGadgetComponents::<C>::default(); num_output_records];

        let new_encrypted_record_hashes = vec![C::EncryptedRecordDigest::default(); num_output_records];

        let memo = [0u8; 64];

        let program_commitment = <C::ProgramCommitmentScheme as CommitmentScheme>::Output::default();
        let program_randomness = <C::ProgramCommitmentScheme as CommitmentScheme>::Randomness::default();

        let local_data_root = C::LocalDataDigest::default();
        let local_data_commitment_randomizers = vec![
            <C::LocalDataCommitmentScheme as CommitmentScheme>::Randomness::default();
            num_input_records + num_output_records
        ];

        let value_balance = AleoAmount::ZERO;
        let network_id: u8 = C::NETWORK_ID;

        Self {
            // Ledger
            ledger_digest: digest,

            // Input records
            old_records,
            old_witnesses,
            old_private_keys,
            old_serial_numbers,

            // Output records
            new_records,
            new_serial_number_nonce_randomness,
            new_commitments,

            new_records_encryption_randomness,
            new_records_encryption_gadget_components,
            new_encrypted_record_hashes,

            // Other stuff
            program_commitment,
            program_randomness,
            local_data_root,
            local_data_commitment_randomizers,
            memo,
            value_balance,
            network_id,
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub fn new(
        // Ledger
        ledger_digest: MerkleTreeDigest<C::RecordCommitmentTreeParameters>,

        // Old records
        old_records: Vec<Record<C>>,
        old_witnesses: Vec<MerklePath<C::RecordCommitmentTreeParameters>>,
        old_private_keys: Vec<PrivateKey<C>>,
        old_serial_numbers: Vec<<C::AccountSignature as SignatureScheme>::PublicKey>,

        // New records
        new_records: Vec<Record<C>>,
        new_serial_number_nonce_randomness: Vec<[u8; 32]>,
        new_commitments: Vec<C::RecordCommitment>,

        new_records_encryption_randomness: Vec<<C::AccountEncryption as EncryptionScheme>::Randomness>,
        new_records_encryption_gadget_components: Vec<RecordEncryptionGadgetComponents<C>>,
        new_encrypted_record_hashes: Vec<C::EncryptedRecordDigest>,

        // Other stuff
        program_commitment: <C::ProgramCommitmentScheme as CommitmentScheme>::Output,
        program_randomness: <C::ProgramCommitmentScheme as CommitmentScheme>::Randomness,

        local_data_root: C::LocalDataDigest,
        local_data_commitment_randomizers: Vec<<C::LocalDataCommitmentScheme as CommitmentScheme>::Randomness>,

        memo: [u8; 64],
        value_balance: AleoAmount,
        network_id: u8,
    ) -> Self {
        let num_input_records = C::NUM_INPUT_RECORDS;
        let num_output_records = C::NUM_OUTPUT_RECORDS;

        assert_eq!(num_input_records, old_records.len());
        assert_eq!(num_input_records, old_witnesses.len());
        assert_eq!(num_input_records, old_private_keys.len());
        assert_eq!(num_input_records, old_serial_numbers.len());

        assert_eq!(num_output_records, new_records.len());
        assert_eq!(num_output_records, new_serial_number_nonce_randomness.len());
        assert_eq!(num_output_records, new_commitments.len());

        assert_eq!(num_output_records, new_records_encryption_randomness.len());
        assert_eq!(num_output_records, new_records_encryption_gadget_components.len());
        assert_eq!(num_output_records, new_encrypted_record_hashes.len());

        // TODO (raychu86) Fix the lengths to be generic
        let record_encoding_length = 7;

        for gadget_components in &new_records_encryption_gadget_components {
            assert_eq!(gadget_components.record_field_elements.len(), record_encoding_length);
            assert_eq!(gadget_components.record_group_encoding.len(), record_encoding_length);
            assert_eq!(gadget_components.ciphertext_selectors.len(), record_encoding_length + 1);
            assert_eq!(gadget_components.fq_high_selectors.len(), record_encoding_length);
            assert_eq!(
                gadget_components.encryption_blinding_exponents.len(),
                record_encoding_length
            );
        }

        Self {
            // Ledger
            ledger_digest,

            // Input records
            old_records,
            old_witnesses,
            old_private_keys,
            old_serial_numbers,

            // Output records
            new_records,
            new_serial_number_nonce_randomness,
            new_commitments,

            new_records_encryption_randomness,
            new_records_encryption_gadget_components,
            new_encrypted_record_hashes,

            // Other stuff
            program_commitment,
            program_randomness,
            local_data_root,
            local_data_commitment_randomizers,
            memo,
            value_balance,
            network_id,
        }
    }
}

impl<C: Parameters> ConstraintSynthesizer<C::InnerScalarField> for InnerCircuit<C> {
    fn generate_constraints<CS: ConstraintSystem<C::InnerScalarField>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        execute_inner_circuit::<C, CS>(
            cs,
            // Ledger
            &self.ledger_digest,
            // Old records
            &self.old_records,
            &self.old_witnesses,
            &self.old_private_keys,
            &self.old_serial_numbers,
            // New records
            &self.new_records,
            &self.new_serial_number_nonce_randomness,
            &self.new_commitments,
            &self.new_records_encryption_randomness,
            &self.new_records_encryption_gadget_components,
            &self.new_encrypted_record_hashes,
            // Other stuff
            &self.program_commitment,
            &self.program_randomness,
            &self.local_data_root,
            &self.local_data_commitment_randomizers,
            &self.memo,
            self.value_balance,
            self.network_id,
        )?;
        Ok(())
    }
}
