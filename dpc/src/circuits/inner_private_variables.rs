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

use crate::{Executable, ExecutionType, Network, Record};
use snarkvm_algorithms::{
    merkle_tree::MerklePath,
    traits::{CommitmentScheme, EncryptionScheme},
};

use anyhow::Result;

#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"))]
pub struct InnerPrivateVariables<N: Network> {
    // Inputs records.
    pub(super) input_records: Vec<Record<N>>,
    pub(super) input_witnesses: Vec<MerklePath<N::CommitmentsTreeParameters>>,
    pub(super) signatures: Vec<N::AccountSignature>,
    // Output records.
    pub(super) output_records: Vec<Record<N>>,
    // Encryption of output records.
    pub(super) encrypted_record_randomizers: Vec<<N::AccountEncryptionScheme as EncryptionScheme>::Randomness>,
    // Executables.
    pub(super) program_ids: Vec<N::ProgramID>,
    pub(super) execution_types: Vec<ExecutionType>,
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
            program_ids: vec![N::noop_program_id(); N::NUM_EXECUTABLES],
            execution_types: vec![ExecutionType::Noop; N::NUM_EXECUTABLES],
            program_randomness: <N::ProgramCommitmentScheme as CommitmentScheme>::Randomness::default(),
            local_data_leaf_randomizers: vec![
                <N::LocalDataCommitmentScheme as CommitmentScheme>::Randomness::default();
                N::NUM_TOTAL_RECORDS
            ],
        }
    }

    pub fn new(
        input_records: Vec<Record<N>>,
        input_witnesses: Vec<MerklePath<N::CommitmentsTreeParameters>>,
        signatures: Vec<N::AccountSignature>,
        output_records: Vec<Record<N>>,
        encrypted_record_randomizers: Vec<<N::AccountEncryptionScheme as EncryptionScheme>::Randomness>,
        executables: &Vec<Executable<N>>,
        program_randomness: <N::ProgramCommitmentScheme as CommitmentScheme>::Randomness,
        local_data_leaf_randomizers: Vec<<N::LocalDataCommitmentScheme as CommitmentScheme>::Randomness>,
    ) -> Result<Self> {
        assert_eq!(N::NUM_INPUT_RECORDS, input_records.len());
        assert_eq!(N::NUM_INPUT_RECORDS, input_witnesses.len());
        assert_eq!(N::NUM_INPUT_RECORDS, signatures.len());
        assert_eq!(N::NUM_OUTPUT_RECORDS, output_records.len());
        assert_eq!(N::NUM_OUTPUT_RECORDS, encrypted_record_randomizers.len());
        assert_eq!(N::NUM_EXECUTABLES, executables.len());
        assert_eq!(N::NUM_TOTAL_RECORDS, local_data_leaf_randomizers.len());

        // Prepare the executable program IDs.
        let program_ids = executables.iter().map(|e| e.program_id()).collect::<Vec<_>>();

        // Prepare the execution types.
        let execution_types = executables
            .iter()
            .map(|e| Ok(e.execution_type()?))
            .collect::<Result<Vec<_>>>()?;

        Ok(Self {
            input_records,
            input_witnesses,
            signatures,
            output_records,
            encrypted_record_randomizers,
            program_ids,
            execution_types,
            program_randomness,
            local_data_leaf_randomizers,
        })
    }
}
