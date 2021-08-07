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

use crate::{InnerPublicVariables, Parameters, Transaction, TransactionScheme};
use snarkvm_algorithms::merkle_tree::MerkleTreeDigest;
use snarkvm_fields::{ConstraintFieldError, ToConstraintField};
use snarkvm_utilities::ToBits;

use anyhow::Result;

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"))]
pub struct OuterPublicVariables<C: Parameters> {
    pub(super) inner_public_variables: InnerPublicVariables<C>,
    pub(super) inner_circuit_id: C::InnerCircuitID,
}

impl<C: Parameters> OuterPublicVariables<C> {
    pub fn blank() -> Self {
        // These inner circuit public variables are allocated as private variables in the outer circuit,
        // as they are not included in the transaction broadcast to the ledger.
        let mut inner_public_variables = InnerPublicVariables::blank();
        inner_public_variables.program_commitment = None;
        inner_public_variables.local_data_root = None;

        Self {
            inner_public_variables,
            inner_circuit_id: C::InnerCircuitID::default(),
        }
    }

    pub fn new(inner_public_variables: &InnerPublicVariables<C>, inner_circuit_id: &C::InnerCircuitID) -> Self {
        assert_eq!(C::NUM_OUTPUT_RECORDS, inner_public_variables.kernel.commitments.len());
        assert_eq!(
            C::NUM_OUTPUT_RECORDS,
            inner_public_variables.encrypted_record_hashes.len()
        );

        // These inner circuit public variables are allocated as private variables in the outer circuit,
        // as they are not included in the transaction broadcast to the ledger.
        let mut inner_public_variables: InnerPublicVariables<C> = inner_public_variables.clone();
        inner_public_variables.program_commitment = None;
        inner_public_variables.local_data_root = None;

        Self {
            inner_public_variables,
            inner_circuit_id: inner_circuit_id.clone(),
        }
    }

    pub fn from(transaction: &Transaction<C>) -> Result<Self> {
        let mut encrypted_record_hashes = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);
        for encrypted_record in transaction.encrypted_records().iter().take(C::NUM_OUTPUT_RECORDS) {
            encrypted_record_hashes.push(encrypted_record.to_hash()?);
        }

        Ok(Self {
            inner_public_variables: InnerPublicVariables {
                kernel: transaction.to_kernel(),
                ledger_digest: transaction.ledger_digest().clone(),
                encrypted_record_hashes,
                // These inner circuit public variables are allocated as private variables in the outer circuit,
                // as they are not included in the transaction broadcast to the ledger.
                program_commitment: None,
                local_data_root: None,
            },
            inner_circuit_id: transaction.inner_circuit_id().clone(),
        })
    }
}

impl<C: Parameters> ToConstraintField<C::OuterScalarField> for OuterPublicVariables<C>
where
    MerkleTreeDigest<C::RecordCommitmentTreeParameters>: ToConstraintField<C::InnerScalarField>,
{
    fn to_field_elements(&self) -> Result<Vec<C::OuterScalarField>, ConstraintFieldError> {
        // In the outer circuit, these two variables must be allocated as witness,
        // as they are not included in the transaction.
        debug_assert!(self.inner_public_variables.program_commitment.is_none());
        debug_assert!(self.inner_public_variables.local_data_root.is_none());

        let mut v = Vec::new();

        // Convert inner circuit public variables into `OuterField` field elements.
        //
        // We allocate the inner circuit public variables using BooleanInput,
        // which allocates nonnative field elements into a circuit, and
        // apply the follow a rule:
        //
        // Alloc the original inputs as bits, then pack them into the new field, in little-endian format.
        for inner_snark_fe in &self.inner_public_variables.to_field_elements()? {
            v.extend_from_slice(&ToConstraintField::<C::OuterScalarField>::to_field_elements(
                inner_snark_fe.to_bits_le().as_slice(),
            )?);
        }

        // Then allocate the inner circuit ID.
        v.extend_from_slice(&self.inner_circuit_id.to_field_elements()?);

        Ok(v)
    }
}
