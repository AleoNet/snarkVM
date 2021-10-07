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

use crate::{AleoAmount, CircuitType, LedgerProof, Network, ProgramExecutable, Record, State, TransactionKernel};
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
                vec![N::CiphertextID::default(); N::NUM_OUTPUT_RECORDS],
                AleoAmount::ZERO,
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

    pub fn new(state: &State<N>, ledger_proof: LedgerProof<N>, signatures: Vec<N::AccountSignature>) -> Result<Self> {
        Ok(Self {
            kernel: state.kernel().clone(),
            input_records: state.input_records().clone(),
            ledger_proof,
            signatures,
            output_records: state.output_records().clone(),
            encrypted_record_randomizers: state.ciphertext_randomizers.clone(),
            circuit_type: state.executable().circuit_type(),
        })
    }

    /// Returns a reference to the transaction kernel.
    pub fn kernel(&self) -> &TransactionKernel<N> {
        &self.kernel
    }
}
