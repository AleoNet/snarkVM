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

use crate::{Parameters, PrivateKey, Record};
use snarkvm_algorithms::{
    merkle_tree::MerklePath,
    traits::{CommitmentScheme, EncryptionScheme},
};

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"))]
pub struct InnerPrivateVariables<C: Parameters> {
    // Inputs records.
    pub(super) input_records: Vec<Record<C>>,
    pub(super) input_witnesses: Vec<MerklePath<C::RecordCommitmentTreeParameters>>,
    pub(super) private_keys: Vec<PrivateKey<C>>,
    // Output records.
    pub(super) output_records: Vec<Record<C>>,
    // Encryption of output records.
    pub(super) encrypted_record_randomizers: Vec<<C::AccountEncryptionScheme as EncryptionScheme>::Randomness>,
    // Commitment to programs and local data.
    pub(super) program_randomness: <C::ProgramCommitmentScheme as CommitmentScheme>::Randomness,
    pub(super) local_data_leaf_randomizers: Vec<<C::LocalDataCommitmentScheme as CommitmentScheme>::Randomness>,
}

impl<C: Parameters> InnerPrivateVariables<C> {
    pub fn blank() -> Self {
        Self {
            input_records: vec![Record::default(); C::NUM_INPUT_RECORDS],
            input_witnesses: vec![MerklePath::default(); C::NUM_INPUT_RECORDS],
            private_keys: vec![PrivateKey::default(); C::NUM_INPUT_RECORDS],
            output_records: vec![Record::default(); C::NUM_OUTPUT_RECORDS],
            encrypted_record_randomizers: vec![
                <C::AccountEncryptionScheme as EncryptionScheme>::Randomness::default();
                C::NUM_OUTPUT_RECORDS
            ],
            program_randomness: <C::ProgramCommitmentScheme as CommitmentScheme>::Randomness::default(),
            local_data_leaf_randomizers: vec![
                <C::LocalDataCommitmentScheme as CommitmentScheme>::Randomness::default();
                C::NUM_TOTAL_RECORDS
            ],
        }
    }

    pub fn new(
        input_records: Vec<Record<C>>,
        old_witnesses: Vec<MerklePath<C::RecordCommitmentTreeParameters>>,
        old_private_keys: Vec<PrivateKey<C>>,
        new_records: Vec<Record<C>>,
        new_records_encryption_randomness: Vec<<C::AccountEncryptionScheme as EncryptionScheme>::Randomness>,
        program_randomness: <C::ProgramCommitmentScheme as CommitmentScheme>::Randomness,
        local_data_commitment_randomizers: Vec<<C::LocalDataCommitmentScheme as CommitmentScheme>::Randomness>,
    ) -> Self {
        assert_eq!(C::NUM_INPUT_RECORDS, input_records.len());
        assert_eq!(C::NUM_INPUT_RECORDS, old_witnesses.len());
        assert_eq!(C::NUM_INPUT_RECORDS, old_private_keys.len());
        assert_eq!(C::NUM_OUTPUT_RECORDS, new_records.len());
        assert_eq!(C::NUM_OUTPUT_RECORDS, new_records_encryption_randomness.len());
        assert_eq!(C::NUM_TOTAL_RECORDS, local_data_commitment_randomizers.len());
        
        Self {
            input_records,
            input_witnesses: old_witnesses,
            private_keys: old_private_keys,
            output_records: new_records,
            encrypted_record_randomizers: new_records_encryption_randomness,
            program_randomness,
            local_data_leaf_randomizers: local_data_commitment_randomizers,
        }
    }
}
