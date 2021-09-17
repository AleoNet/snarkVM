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

use crate::{Network, Record};
use snarkvm_algorithms::{
    merkle_tree::MerklePath,
    traits::{CommitmentScheme, EncryptionScheme},
};

#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"))]
pub struct InnerPrivateVariables<N: Network> {
    // Inputs records.
    pub(super) input_records: Vec<Record<N>>,
    pub(super) input_witnesses: Vec<MerklePath<N::LedgerCommitmentsTreeParameters>>,
    pub(super) signatures: Vec<N::AccountSignature>,
    // Output records.
    pub(super) output_records: Vec<Record<N>>,
    // Encryption of output records.
    pub(super) encrypted_record_randomizers: Vec<<N::AccountEncryptionScheme as EncryptionScheme>::Randomness>,
    // Commitment to programs and local data.
    pub(super) program_randomness: <N::ProgramCommitmentScheme as CommitmentScheme>::Randomness,
    pub(super) local_data_leaf_randomizers: Vec<<N::LocalDataCommitmentScheme as CommitmentScheme>::Randomness>,
}

impl<N: Network> InnerPrivateVariables<N> {
    pub fn blank() -> Self {
        Self {
            input_records: vec![Record::default(); N::NUM_INPUT_RECORDS],
            input_witnesses: vec![MerklePath::default(); N::NUM_INPUT_RECORDS],
            signatures: vec![N::AccountSignature::default(); N::NUM_INPUT_RECORDS],
            output_records: vec![Record::default(); N::NUM_OUTPUT_RECORDS],
            encrypted_record_randomizers: vec![
                <N::AccountEncryptionScheme as EncryptionScheme>::Randomness::default();
                N::NUM_OUTPUT_RECORDS
            ],
            program_randomness: <N::ProgramCommitmentScheme as CommitmentScheme>::Randomness::default(),
            local_data_leaf_randomizers: vec![
                <N::LocalDataCommitmentScheme as CommitmentScheme>::Randomness::default();
                N::NUM_TOTAL_RECORDS
            ],
        }
    }

    pub fn new(
        input_records: Vec<Record<N>>,
        input_witnesses: Vec<MerklePath<N::LedgerCommitmentsTreeParameters>>,
        signatures: Vec<N::AccountSignature>,
        output_records: Vec<Record<N>>,
        encrypted_record_randomizers: Vec<<N::AccountEncryptionScheme as EncryptionScheme>::Randomness>,
        program_randomness: <N::ProgramCommitmentScheme as CommitmentScheme>::Randomness,
        local_data_leaf_randomizers: Vec<<N::LocalDataCommitmentScheme as CommitmentScheme>::Randomness>,
    ) -> Self {
        assert_eq!(N::NUM_INPUT_RECORDS, input_records.len());
        assert_eq!(N::NUM_INPUT_RECORDS, input_witnesses.len());
        assert_eq!(N::NUM_INPUT_RECORDS, signatures.len());
        assert_eq!(N::NUM_OUTPUT_RECORDS, output_records.len());
        assert_eq!(N::NUM_OUTPUT_RECORDS, encrypted_record_randomizers.len());
        assert_eq!(N::NUM_TOTAL_RECORDS, local_data_leaf_randomizers.len());

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
