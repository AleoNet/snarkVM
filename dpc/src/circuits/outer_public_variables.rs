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

use crate::{InnerPublicVariables, Network, Transaction, TransactionScheme};
use snarkvm_algorithms::merkle_tree::MerkleTreeDigest;
use snarkvm_fields::{ConstraintFieldError, ToConstraintField};
use snarkvm_utilities::ToBits;

use anyhow::Result;

#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"))]
pub struct OuterPublicVariables<N: Network> {
    pub(super) inner_public_variables: InnerPublicVariables<N>,
    pub(super) inner_circuit_id: N::InnerCircuitID,
}

impl<N: Network> OuterPublicVariables<N> {
    pub fn blank() -> Self {
        // This inner circuit public variable is allocated as a private variable in the outer circuit,
        // as it is not included in the transaction broadcast to the ledger.
        let mut inner_public_variables = InnerPublicVariables::blank();
        inner_public_variables.program_id = None;

        Self {
            inner_public_variables,
            inner_circuit_id: N::InnerCircuitID::default(),
        }
    }

    pub fn new(inner_public_variables: &InnerPublicVariables<N>, inner_circuit_id: &N::InnerCircuitID) -> Self {
        assert_eq!(N::NUM_OUTPUT_RECORDS, inner_public_variables.encrypted_record_ids.len());

        // This inner circuit public variable is allocated as a private variable in the outer circuit,
        // as it is not included in the transaction broadcast to the ledger.
        let mut inner_public_variables: InnerPublicVariables<N> = inner_public_variables.clone();
        inner_public_variables.program_id = None;

        Self {
            inner_public_variables,
            inner_circuit_id: inner_circuit_id.clone(),
        }
    }

    pub fn from(transaction: &Transaction<N>) -> Result<Self> {
        Ok(Self {
            inner_public_variables: InnerPublicVariables {
                transaction_id: transaction.to_transaction_id()?,
                ledger_digest: transaction.ledger_digest().clone(),
                encrypted_record_ids: transaction.to_encrypted_record_ids()?,
                // This inner circuit public variable is allocated as a private variable in the outer circuit,
                // as it is not included in the transaction broadcast to the ledger.
                program_id: None,
            },
            inner_circuit_id: transaction.inner_circuit_id().clone(),
        })
    }
}

impl<N: Network> ToConstraintField<N::OuterScalarField> for OuterPublicVariables<N>
where
    MerkleTreeDigest<N::CommitmentsTreeParameters>: ToConstraintField<N::InnerScalarField>,
{
    fn to_field_elements(&self) -> Result<Vec<N::OuterScalarField>, ConstraintFieldError> {
        // In the outer circuit, this variable must be allocated as private input,
        // as it is not included in the transaction.
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
                inner_snark_fe.to_bits_le().as_slice(),
            )?);
        }

        // Then allocate the inner circuit ID.
        v.extend_from_slice(&self.inner_circuit_id.to_field_elements()?);

        Ok(v)
    }
}
