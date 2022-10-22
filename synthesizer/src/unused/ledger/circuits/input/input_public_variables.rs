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
pub struct InputPublicVariables<N: Network> {
    /// The serial number of the input record.
    serial_number: N::SerialNumber,
    /// The commitments on the input record value.
    input_value_commitment: N::ValueCommitment,
    ledger_root: N::LedgerRoot,
    local_transitions_root: N::TransactionID,
    // These are required in natively verifying an inner circuit proof.
    // However for verification in the outer circuit, these must be provided as witness.
    /// Program ID
    pub(super) program_id: Option<N::ProgramID>,
}

impl<N: Network> InputPublicVariables<N> {
    pub(crate) fn blank() -> Self {
        Self {
            serial_number: Default::default(),
            input_value_commitment: N::ProgramAffineCurve::default().into(),
            local_transitions_root: Default::default(),
            ledger_root: Default::default(),
            program_id: Some(N::ProgramID::default()),
        }
    }

    pub(crate) fn new(
        serial_number: N::SerialNumber,
        input_value_commitment: N::ValueCommitment,
        ledger_root: N::LedgerRoot,
        local_transitions_root: N::TransactionID,
        program_id: Option<N::ProgramID>,
    ) -> Self {
        Self { serial_number, input_value_commitment, ledger_root, local_transitions_root, program_id }
    }

    /// Returns a reference to the serial numbers.
    pub(crate) fn serial_number(&self) -> &N::SerialNumber {
        &self.serial_number
    }

    /// Returns the commitments on the input record value.
    pub(crate) fn input_value_commitment(&self) -> &N::ValueCommitment {
        &self.input_value_commitment
    }

    /// Returns the ledger root.
    pub(crate) fn ledger_root(&self) -> N::LedgerRoot {
        self.ledger_root
    }

    pub(crate) fn local_transitions_root(&self) -> N::TransactionID {
        self.local_transitions_root
    }
}

impl<N: Network> ToConstraintField<N::InnerScalarField> for InputPublicVariables<N> {
    fn to_field_elements(&self) -> Result<Vec<N::InnerScalarField>, ConstraintFieldError> {
        let mut v = Vec::new();
        v.extend_from_slice(&self.ledger_root.to_field_elements()?);
        v.extend_from_slice(&self.local_transitions_root.to_field_elements()?);

        if let Some(program_id) = &self.program_id {
            v.extend_from_slice(&program_id.to_bytes_le()?.to_field_elements()?);
        } else {
            v.extend_from_slice(&vec![0u8; N::PROGRAM_ID_SIZE_IN_BYTES].to_field_elements()?);
        }

        v.extend_from_slice(&self.serial_number.to_field_elements()?);
        v.extend_from_slice(&self.input_value_commitment.to_field_elements()?);

        Ok(v)
    }
}
