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

use crate::{AleoAmount, InnerPublicVariables, Network};
use snarkvm_fields::{ConstraintFieldError, ToConstraintField};
use snarkvm_utilities::ToBits;

use anyhow::Result;

#[derive(Clone, Debug)]
pub struct OuterPublicVariables<N: Network> {
    inner_public_variables: InnerPublicVariables<N>,
    inner_circuit_id: N::InnerCircuitID,
}

impl<N: Network> OuterPublicVariables<N> {
    pub(crate) fn blank() -> Self {
        // These inner circuit public variables are allocated as private variables in the outer circuit,
        // as they are not included in the transaction broadcast to the ledger.
        let mut inner_public_variables = InnerPublicVariables::blank();
        inner_public_variables.program_id = None;

        Self {
            inner_public_variables,
            inner_circuit_id: N::InnerCircuitID::default(),
        }
    }

    pub(crate) fn new(inner_public_variables: InnerPublicVariables<N>, inner_circuit_id: &N::InnerCircuitID) -> Self {
        // These inner circuit public variables are allocated as private variables in the outer circuit,
        // as they are not included in the transaction broadcast to the ledger.
        let mut inner_public_variables: InnerPublicVariables<N> = inner_public_variables;
        inner_public_variables.program_id = None;

        Self {
            inner_public_variables,
            inner_circuit_id: *inner_circuit_id,
        }
    }

    /// Returns the transition ID.
    pub(crate) fn transition_id(&self) -> N::TransitionID {
        self.inner_public_variables.transition_id()
    }

    /// Returns the value balance of the transition.
    pub(crate) fn value_balance(&self) -> AleoAmount {
        self.inner_public_variables.value_balance()
    }

    /// Returns the ledger root.
    pub(crate) fn ledger_root(&self) -> N::LedgerRoot {
        self.inner_public_variables.ledger_root()
    }

    pub(crate) fn local_transitions_root(&self) -> N::TransactionID {
        self.inner_public_variables.local_transitions_root()
    }

    pub(crate) fn inner_circuit_id(&self) -> N::InnerCircuitID {
        self.inner_circuit_id
    }
}

impl<N: Network> ToConstraintField<N::OuterScalarField> for OuterPublicVariables<N> {
    fn to_field_elements(&self) -> Result<Vec<N::OuterScalarField>, ConstraintFieldError> {
        // In the outer circuit, these two variables must be allocated as witness,
        // as they are not included in the transaction.
        debug_assert!(self.inner_public_variables.program_id.is_none());

        let mut v = Vec::new();

        // Convert inner circuit public variables into `OuterField` field elements.
        //
        // We allocate the inner circuit public variables using BooleanInput,
        // which allocates nonnative field elements into a circuit, and
        // apply the follow a rule:
        //
        // Alloc the original inputs as bits, then pack them into the new field, in little-endian format.
        for inner_snark_fe in &self.inner_public_variables.to_field_elements()? {
            v.extend_from_slice(&ToConstraintField::<N::OuterScalarField>::to_field_elements(
                inner_snark_fe.to_bits_le().as_bitslice(),
            )?);
        }

        // Then allocate the inner circuit ID.
        v.extend_from_slice(&self.inner_circuit_id.to_field_elements()?);

        Ok(v)
    }
}
