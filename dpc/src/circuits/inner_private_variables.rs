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

use crate::{Parameters, Record};
use snarkvm_algorithms::{
    merkle_tree::MerklePath,
    traits::{CommitmentScheme, EncryptionScheme},
};

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"))]
pub struct InnerPrivateVariables<C: Parameters> {
    // Inputs records.
    pub(super) input_records: Vec<Record<C>>,
    pub(super) input_witnesses: Vec<MerklePath<C::LedgerCommitmentsTreeParameters>>,
    pub(super) signatures: Vec<C::AccountSignature>,
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
            signatures: vec![C::AccountSignature::default(); C::NUM_INPUT_RECORDS],
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
        input_witnesses: Vec<MerklePath<C::LedgerCommitmentsTreeParameters>>,
        signatures: Vec<C::AccountSignature>,
        output_records: Vec<Record<C>>,
        encrypted_record_randomizers: Vec<<C::AccountEncryptionScheme as EncryptionScheme>::Randomness>,
        program_randomness: <C::ProgramCommitmentScheme as CommitmentScheme>::Randomness,
        local_data_leaf_randomizers: Vec<<C::LocalDataCommitmentScheme as CommitmentScheme>::Randomness>,
    ) -> Self {
        assert_eq!(C::NUM_INPUT_RECORDS, input_records.len());
        assert_eq!(C::NUM_INPUT_RECORDS, input_witnesses.len());
        assert_eq!(C::NUM_INPUT_RECORDS, signatures.len());
        assert_eq!(C::NUM_OUTPUT_RECORDS, output_records.len());
        assert_eq!(C::NUM_OUTPUT_RECORDS, encrypted_record_randomizers.len());
        assert_eq!(C::NUM_TOTAL_RECORDS, local_data_leaf_randomizers.len());

        Self {
            input_records,
            input_witnesses,
            signatures,
            output_records,
            encrypted_record_randomizers,
            program_randomness,
            local_data_leaf_randomizers,
        }
    }
}
