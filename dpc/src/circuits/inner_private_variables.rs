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
    AleoAmount,
    CircuitType,
    Executable,
    LedgerProof,
    Memo,
    Network,
    ProgramExecutable,
    Record,
    TransactionKernel,
};
use snarkvm_algorithms::traits::EncryptionScheme;

use anyhow::Result;

#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"))]
pub struct InnerPrivateVariables<N: Network> {
    /// Transaction kernel
    kernel: TransactionKernel<N>,
    // Inputs records.
    pub(super) input_records: Vec<Record<N>>,
    pub(super) ledger_proof: LedgerProof<N>,
    pub(super) signatures: Vec<N::AccountSignature>,
    // Output records.
    pub(super) output_records: Vec<Record<N>>,
    // Encryption of output records.
    pub(super) encrypted_record_randomizers: Vec<<N::AccountEncryptionScheme as EncryptionScheme>::Randomness>,
    // Executable.
    pub(super) circuit_type: CircuitType,
}

impl<N: Network> InnerPrivateVariables<N> {
    pub fn blank() -> Self {
        Self {
            kernel: TransactionKernel::new(
                vec![N::SerialNumber::default(); N::NUM_INPUT_RECORDS],
                vec![N::Commitment::default(); N::NUM_OUTPUT_RECORDS],
                AleoAmount::ZERO,
                Memo::default(),
            )
            .expect("Failed to instantiate a blank transaction kernel"),
            input_records: vec![Record::default(); N::NUM_INPUT_RECORDS],
            ledger_proof: Default::default(),
            signatures: vec![N::AccountSignature::default(); N::NUM_INPUT_RECORDS],
            output_records: vec![Record::default(); N::NUM_OUTPUT_RECORDS],
            encrypted_record_randomizers: vec![
                <N::AccountEncryptionScheme as EncryptionScheme>::Randomness::default();
                N::NUM_OUTPUT_RECORDS
            ],
            circuit_type: CircuitType::Noop,
        }
    }

    pub fn new(
        kernel: &TransactionKernel<N>,
        input_records: Vec<Record<N>>,
        ledger_proof: LedgerProof<N>,
        signatures: Vec<N::AccountSignature>,
        output_records: Vec<Record<N>>,
        encrypted_record_randomizers: Vec<<N::AccountEncryptionScheme as EncryptionScheme>::Randomness>,
        executable: &Executable<N>,
    ) -> Result<Self> {
        assert!(kernel.is_valid());
        assert_eq!(N::NUM_INPUT_RECORDS, input_records.len());
        assert_eq!(N::NUM_INPUT_RECORDS, signatures.len());
        assert_eq!(N::NUM_OUTPUT_RECORDS, output_records.len());
        assert_eq!(N::NUM_OUTPUT_RECORDS, encrypted_record_randomizers.len());

        Ok(Self {
            kernel: kernel.clone(),
            input_records,
            ledger_proof,
            signatures,
            output_records,
            encrypted_record_randomizers,
            circuit_type: executable.circuit_type(),
        })
    }

    /// Returns a reference to the transaction kernel.
    pub fn kernel(&self) -> &TransactionKernel<N> {
        &self.kernel
    }
}
