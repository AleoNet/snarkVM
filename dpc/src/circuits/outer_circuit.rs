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

use crate::{execute_outer_circuit, Execution, OuterPrivateVariables, OuterPublicVariables, Parameters};
use snarkvm_algorithms::{merkle_tree::MerkleTreeDigest, traits::SNARK};
use snarkvm_fields::ToConstraintField;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSynthesizer, ConstraintSystem};

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"))]
pub struct OuterCircuit<C: Parameters> {
    public: OuterPublicVariables<C>,
    private: OuterPrivateVariables<C>,
}

impl<C: Parameters> OuterCircuit<C> {
    pub fn blank(
        inner_snark_vk: <C::InnerSNARK as SNARK>::VerifyingKey,
        inner_snark_proof: <C::InnerSNARK as SNARK>::Proof,
        execution: Execution<C>,
    ) -> Self {
        Self {
            public: OuterPublicVariables::blank(),
            private: OuterPrivateVariables::blank(inner_snark_vk, inner_snark_proof, execution),
        }
    }

    pub fn new(public: OuterPublicVariables<C>, private: OuterPrivateVariables<C>) -> Self {
        Self { public, private }
    }
}

impl<C: Parameters> ConstraintSynthesizer<C::OuterScalarField> for OuterCircuit<C>
where
    MerkleTreeDigest<C::RecordCommitmentTreeParameters>: ToConstraintField<C::InnerScalarField>,
{
    fn generate_constraints<CS: ConstraintSystem<C::OuterScalarField>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        execute_outer_circuit::<C, CS>(cs, &self.public, &self.private)
    }
}
