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

use crate::{InnerCircuitVerifierInput, Parameters};
use snarkvm_algorithms::{
    merkle_tree::MerkleTreeDigest,
    traits::{CommitmentScheme, CRH},
};
use snarkvm_fields::{ConstraintFieldError, ToConstraintField};
use snarkvm_utilities::ToBits;

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"))]
pub struct OuterCircuitVerifierInput<C: Parameters> {
    pub inner_snark_verifier_input: InnerCircuitVerifierInput<C>,
    pub inner_circuit_id: <C::InnerCircuitIDCRH as CRH>::Output,
}

impl<C: Parameters> ToConstraintField<C::OuterScalarField> for OuterCircuitVerifierInput<C>
where
    <C::AccountCommitmentScheme as CommitmentScheme>::Output: ToConstraintField<C::InnerScalarField>,
    MerkleTreeDigest<C::RecordCommitmentTreeParameters>: ToConstraintField<C::InnerScalarField>,
{
    fn to_field_elements(&self) -> Result<Vec<C::OuterScalarField>, ConstraintFieldError> {
        let mut v = Vec::new();

        // Convert inner snark verifier inputs into `OuterField` field elements
        let inner_snark_field_elements = &self.inner_snark_verifier_input.to_field_elements()?;

        // We can allocate the inner snark verifier inputs as follows.
        //
        // This is because BooleanInput, which is the norm of allocating nonnative field elements into a circuit,
        // always follow a rule: alloc the original inputs as bits, and pack them into the new fields, all in the
        // little-endian format.
        for inner_snark_fe in inner_snark_field_elements {
            v.extend_from_slice(&ToConstraintField::<C::OuterScalarField>::to_field_elements(
                inner_snark_fe.to_bits_le().as_slice(),
            )?);
        }

        v.extend_from_slice(&self.inner_circuit_id.to_field_elements()?);
        Ok(v)
    }
}
