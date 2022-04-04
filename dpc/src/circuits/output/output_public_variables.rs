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

use crate::Network;
use snarkvm_fields::{ConstraintFieldError, ToConstraintField};
use snarkvm_utilities::ToBytes;

use anyhow::Result;

#[derive(Clone, Debug)]
pub struct OutputPublicVariables<N: Network> {
    /// The commitment of the output record.
    commitment: N::Commitment,
    /// The commitments on the output record value.
    output_value_commitment: N::ValueCommitment,
    // These are required in natively verifying an inner circuit proof.
    // However for verification in the outer circuit, these must be provided as witness.
    /// Program ID
    pub(super) program_id: Option<N::ProgramID>,
}

impl<N: Network> OutputPublicVariables<N> {
    pub(crate) fn blank() -> Self {
        Self {
            commitment: Default::default(),
            output_value_commitment: N::ProgramAffineCurve::default().into(),
            program_id: Some(N::ProgramID::default()),
        }
    }

    pub(crate) fn new(
        commitment: N::Commitment,
        output_value_commitment: N::ValueCommitment,
        program_id: Option<N::ProgramID>,
    ) -> Self {
        Self { commitment, output_value_commitment, program_id }
    }

    /// Returns a reference to the serial numbers.
    pub(crate) fn commitment(&self) -> &N::Commitment {
        &self.commitment
    }

    /// Returns the commitments on the output record value.
    pub(crate) fn output_value_commitment(&self) -> &N::ValueCommitment {
        &self.output_value_commitment
    }
}

impl<N: Network> ToConstraintField<N::InnerScalarField> for OutputPublicVariables<N> {
    fn to_field_elements(&self) -> Result<Vec<N::InnerScalarField>, ConstraintFieldError> {
        let mut v = Vec::new();

        if let Some(program_id) = &self.program_id {
            v.extend_from_slice(&program_id.to_bytes_le()?.to_field_elements()?);
        } else {
            v.extend_from_slice(&vec![0u8; N::PROGRAM_ID_SIZE_IN_BYTES].to_field_elements()?);
        }

        v.extend_from_slice(&self.commitment.to_field_elements()?);
        v.extend_from_slice(&self.output_value_commitment.to_field_elements()?);

        Ok(v)
    }
}
