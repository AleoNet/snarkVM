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

use crate::{Execution, Parameters};
use snarkvm_algorithms::traits::{CommitmentScheme, SNARK};

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"))]
pub struct OuterPrivateVariables<C: Parameters> {
    pub(super) inner_snark_vk: <C::InnerSNARK as SNARK>::VerifyingKey,
    pub(super) inner_snark_proof: <C::InnerSNARK as SNARK>::Proof,
    pub(super) program_proofs: Vec<Execution<C>>,
    pub(super) program_commitment: <C::ProgramCommitmentScheme as CommitmentScheme>::Output,
    pub(super) program_randomness: <C::ProgramCommitmentScheme as CommitmentScheme>::Randomness,
    pub(super) local_data_root: C::LocalDataRoot,
}

impl<C: Parameters> OuterPrivateVariables<C> {
    pub fn blank(
        inner_snark_vk: <C::InnerSNARK as SNARK>::VerifyingKey,
        inner_snark_proof: <C::InnerSNARK as SNARK>::Proof,
        execution: Execution<C>,
    ) -> Self {
        Self {
            inner_snark_vk,
            inner_snark_proof,
            program_proofs: vec![execution.clone(); C::NUM_TOTAL_RECORDS],
            program_commitment: <C::ProgramCommitmentScheme as CommitmentScheme>::Output::default(),
            program_randomness: <C::ProgramCommitmentScheme as CommitmentScheme>::Randomness::default(),
            local_data_root: C::LocalDataRoot::default(),
        }
    }

    pub fn new(
        inner_snark_vk: <C::InnerSNARK as SNARK>::VerifyingKey,
        inner_snark_proof: <C::InnerSNARK as SNARK>::Proof,
        program_proofs: Vec<Execution<C>>,
        program_commitment: <C::ProgramCommitmentScheme as CommitmentScheme>::Output,
        program_randomness: <C::ProgramCommitmentScheme as CommitmentScheme>::Randomness,
        local_data_root: C::LocalDataRoot,
    ) -> Self {
        assert_eq!(C::NUM_TOTAL_RECORDS, program_proofs.len());
        Self {
            inner_snark_vk,
            inner_snark_proof,
            program_proofs,
            program_commitment,
            program_randomness,
            local_data_root,
        }
    }
}
