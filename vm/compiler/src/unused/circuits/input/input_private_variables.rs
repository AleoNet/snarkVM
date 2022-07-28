// Copyright (C) 2019-2022 Aleo Systems Inc.
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

use crate::{LedgerProof, Network, Record};
use snarkvm_algorithms::traits::SignatureScheme;

use anyhow::Result;

#[derive(Clone)]
pub struct InputPrivateVariables<N: Network> {
    // Inputs.
    pub(super) input_record: Record<N>,
    pub(super) ledger_proof: LedgerProof<N>,
    pub(super) signature: N::AccountSignature,

    pub(super) input_value_commitment_randomness: N::ProgramScalarField,
}

impl<N: Network> InputPrivateVariables<N> {
    pub(crate) fn blank() -> Self {
        Self {
            input_record: Record::default(),
            ledger_proof: Default::default(),
            signature: <N::AccountSignatureScheme as SignatureScheme>::Signature::default().into(),
            input_value_commitment_randomness: Default::default(),
        }
    }

    pub(crate) fn new(
        input_record: Record<N>,
        ledger_proof: LedgerProof<N>,
        signature: N::AccountSignature,
        input_value_commitment_randomness: N::ProgramScalarField,
    ) -> Result<Self> {
        Ok(Self { input_record, ledger_proof, signature, input_value_commitment_randomness })
    }

    // pub(crate) fn new(request: &Request<N>, response: &Response<N>) -> Result<Self> {
    //     Ok(Self {
    //         input_record: request.records().clone(),
    //         ledger_proofs: request.ledger_proofs().clone(),
    //         signature: request.signature().clone(),
    //         input_value_commitment_randomness: response.input_value_commitment_randomness().clone(),
    //     })
    // }
}
