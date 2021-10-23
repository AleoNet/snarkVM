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

use crate::Network;
use snarkvm_fields::{ConstraintFieldError, ToConstraintField};
use snarkvm_utilities::ToBits;

use anyhow::Result;

#[derive(Clone, Debug)]
pub struct OuterPublicVariables<N: Network> {
    transition_id: N::TransitionID,
    ledger_root: N::LedgerRoot,
    local_transitions_root: N::TransactionID,
    inner_circuit_id: N::InnerCircuitID,
}

impl<N: Network> OuterPublicVariables<N> {
    pub(crate) fn blank() -> Self {
        Self {
            transition_id: N::TransitionID::default(),
            ledger_root: N::LedgerRoot::default(),
            local_transitions_root: N::TransactionID::default(),
            inner_circuit_id: N::InnerCircuitID::default(),
        }
    }

    pub(crate) fn new(
        transition_id: N::TransitionID,
        ledger_root: N::LedgerRoot,
        local_transitions_root: N::TransactionID,
        inner_circuit_id: N::InnerCircuitID,
    ) -> Self {
        Self {
            transition_id,
            ledger_root,
            local_transitions_root,
            inner_circuit_id,
        }
    }

    /// Returns the transition ID.
    pub(crate) fn transition_id(&self) -> N::TransitionID {
        self.transition_id
    }

    /// Returns the ledger root.
    pub(crate) fn ledger_root(&self) -> N::LedgerRoot {
        self.ledger_root
    }

    pub(crate) fn local_transitions_root(&self) -> N::TransactionID {
        self.local_transitions_root
    }

    pub(crate) fn inner_circuit_id(&self) -> N::InnerCircuitID {
        self.inner_circuit_id
    }
}

impl<N: Network> ToConstraintField<N::OuterScalarField> for OuterPublicVariables<N> {
    fn to_field_elements(&self) -> Result<Vec<N::OuterScalarField>, ConstraintFieldError> {
        let mut v = Vec::new();

        // Convert inner circuit public variables into `OuterField` field elements.
        //
        // We allocate the inner circuit public variables using BooleanInput,
        // which allocates nonnative field elements into a circuit, and
        // apply the follow a rule:
        //
        // Alloc the original inputs as bits, then pack them into the new field, in little-endian format.
        for ledger_root_fe in &self.ledger_root.to_field_elements()? {
            v.extend_from_slice(&ToConstraintField::<N::OuterScalarField>::to_field_elements(
                ledger_root_fe.to_bits_le().as_slice(),
            )?);
        }
        for local_transitions_root_fe in &self.local_transitions_root.to_field_elements()? {
            v.extend_from_slice(&ToConstraintField::<N::OuterScalarField>::to_field_elements(
                local_transitions_root_fe.to_bits_le().as_slice(),
            )?);
        }
        for transition_id_fe in &self.transition_id.to_field_elements()? {
            v.extend_from_slice(&ToConstraintField::<N::OuterScalarField>::to_field_elements(
                transition_id_fe.to_bits_le().as_slice(),
            )?);
        }

        // Then allocate the inner circuit ID.
        v.extend_from_slice(&self.inner_circuit_id.to_field_elements()?);

        Ok(v)
    }
}
