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

use crate::{FunctionType, LedgerProof, Network, Record, Request, Response};
use snarkvm_algorithms::traits::{EncryptionScheme, SignatureScheme};

use anyhow::Result;

#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"))]
pub struct InnerPrivateVariables<N: Network> {
    // Inputs.
    pub(super) input_records: Vec<Record<N>>,
    pub(super) ledger_proofs: Vec<LedgerProof<N>>,
    pub(super) signature: N::AccountSignature,
    pub(super) function_type: FunctionType,

    // Outputs.
    pub(super) output_records: Vec<Record<N>>,
    pub(super) encryption_randomness: Vec<<N::AccountEncryptionScheme as EncryptionScheme>::ScalarRandomness>,
}

impl<N: Network> InnerPrivateVariables<N> {
    pub(crate) fn blank() -> Self
    where
        Record<N>: Default,
    {
        Self {
            input_records: vec![Record::default(); N::NUM_INPUT_RECORDS],
            ledger_proofs: vec![Default::default(); N::NUM_INPUT_RECORDS],
            signature: <N::AccountSignatureScheme as SignatureScheme>::Signature::default().into(),
            function_type: FunctionType::Noop,
            output_records: vec![Record::default(); N::NUM_OUTPUT_RECORDS],
            encryption_randomness: vec![
                <N::AccountEncryptionScheme as EncryptionScheme>::ScalarRandomness::default();
                N::NUM_OUTPUT_RECORDS
            ],
        }
    }

    pub(crate) fn new(request: &Request<N>, response: &Response<N>) -> Result<Self> {
        Ok(Self {
            input_records: request.records().clone(),
            ledger_proofs: request.ledger_proofs().clone(),
            signature: request.signature().clone(),
            function_type: request.function_type(),
            output_records: response.records().clone(),
            encryption_randomness: response.encryption_randomness().clone(),
        })
    }
}
