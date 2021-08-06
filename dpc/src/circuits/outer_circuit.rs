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

use crate::{execute_outer_circuit, Execution, OuterPublicVariables, Parameters};
use snarkvm_algorithms::{
    merkle_tree::MerkleTreeDigest,
    traits::{CommitmentScheme, SNARK},
};
use snarkvm_fields::ToConstraintField;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSynthesizer, ConstraintSystem};

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"))]
pub struct OuterCircuit<C: Parameters> {
    public: OuterPublicVariables<C>,

    // Inner snark verifier private inputs
    inner_snark_vk: <C::InnerSNARK as SNARK>::VerifyingKey,
    inner_snark_proof: <C::InnerSNARK as SNARK>::Proof,

    program_proofs: Vec<Execution<C>>,
    program_commitment: <C::ProgramCommitmentScheme as CommitmentScheme>::Output,
    program_randomness: <C::ProgramCommitmentScheme as CommitmentScheme>::Randomness,
    local_data_root: C::LocalDataRoot,
}

impl<C: Parameters> OuterCircuit<C> {
    pub fn blank(
        inner_snark_vk: <C::InnerSNARK as SNARK>::VerifyingKey,
        inner_snark_proof: <C::InnerSNARK as SNARK>::Proof,
        program_snark_vk_and_proof: Execution<C>,
    ) -> Self {
        let program_proofs = vec![program_snark_vk_and_proof.clone(); C::NUM_TOTAL_RECORDS];
        let program_commitment = <C::ProgramCommitmentScheme as CommitmentScheme>::Output::default();
        let program_randomness = <C::ProgramCommitmentScheme as CommitmentScheme>::Randomness::default();
        let local_data_root = C::LocalDataRoot::default();

        Self {
            public: OuterPublicVariables::blank(),
            inner_snark_vk,
            inner_snark_proof,
            program_proofs,
            program_commitment,
            program_randomness,
            local_data_root,
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub fn new(
        public: OuterPublicVariables<C>,

        // Inner SNARK private inputs
        inner_snark_vk: <C::InnerSNARK as SNARK>::VerifyingKey,
        inner_snark_proof: <C::InnerSNARK as SNARK>::Proof,

        // Private program input = Verification key and input
        // Commitment contains commitment to hash of death program vk.
        program_proofs: Vec<Execution<C>>,
        program_commitment: <C::ProgramCommitmentScheme as CommitmentScheme>::Output,
        program_randomness: <C::ProgramCommitmentScheme as CommitmentScheme>::Randomness,
        local_data_root: C::LocalDataRoot,
    ) -> Self {
        assert_eq!(C::NUM_TOTAL_RECORDS, program_proofs.len());
        assert_eq!(
            C::NUM_OUTPUT_RECORDS,
            public.inner_public_variables.kernel.commitments.len()
        );
        assert_eq!(
            C::NUM_OUTPUT_RECORDS,
            public.inner_public_variables.encrypted_record_hashes.len()
        );

        Self {
            public,
            inner_snark_vk,
            inner_snark_proof,
            program_proofs,
            program_commitment,
            program_randomness,
            local_data_root,
        }
    }
}

impl<C: Parameters> ConstraintSynthesizer<C::OuterScalarField> for OuterCircuit<C>
where
    <C::AccountCommitmentScheme as CommitmentScheme>::Output: ToConstraintField<C::InnerScalarField>,
    MerkleTreeDigest<C::RecordCommitmentTreeParameters>: ToConstraintField<C::InnerScalarField>,
{
    fn generate_constraints<CS: ConstraintSystem<C::OuterScalarField>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        execute_outer_circuit::<C, CS>(
            cs,
            &self.public,
            &self.inner_snark_vk,
            &self.inner_snark_proof,
            &self.program_proofs,
            &self.program_commitment,
            &self.program_randomness,
            &self.local_data_root,
        )?;
        Ok(())
    }
}
