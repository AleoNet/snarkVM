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

use crate::{
    fft::{DensePolynomial, EvaluationDomain},
    polycommit::LabeledPolynomial,
    snark::marlin::{
        ahp::{indexer::Circuit, prover::ProverConstraintSystem, verifier::VerifierFirstMessage},
        AHPError,
        MarlinMode,
    },
};
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::SynthesisError;

/// State for the AHP prover.
pub struct ProverState<'a, F: PrimeField, MM: MarlinMode> {
    pub(super) padded_public_variables: Vec<F>,
    pub(super) private_variables: Vec<F>,
    /// Query bound b
    pub(super) zk_bound: usize,
    /// Az.
    pub(super) z_a: Option<Vec<F>>,
    /// Bz.
    pub(super) z_b: Option<Vec<F>>,

    pub(super) w_poly: Option<LabeledPolynomial<F>>,
    pub(super) mz_polys: Option<(LabeledPolynomial<F>, LabeledPolynomial<F>)>,
    pub(super) mz_poly_randomizer: Option<(F, F)>,

    pub(super) index: &'a Circuit<F, MM>,

    /// The challenges sent by the verifier in the first round
    pub(super) verifier_first_message: Option<VerifierFirstMessage<F>>,

    /// the blinding polynomial for the first round
    pub(super) mask_poly: Option<LabeledPolynomial<F>>,

    /// A domain that is sized for the public input.
    pub(super) input_domain: EvaluationDomain<F>,

    /// A domain that is sized for the number of constraints.
    pub(super) constraint_domain: EvaluationDomain<F>,

    /// A domain that is sized for the number of non-zero elements in A.
    pub(super) non_zero_a_domain: EvaluationDomain<F>,
    /// A domain that is sized for the number of non-zero elements in B.
    pub(super) non_zero_b_domain: EvaluationDomain<F>,
    /// A domain that is sized for the number of non-zero elements in C.
    pub(super) non_zero_c_domain: EvaluationDomain<F>,

    /// Polynomials involved in the holographic sumcheck.
    pub(super) lhs_polynomials: Option<[DensePolynomial<F>; 3]>,
    /// Polynomials involved in the holographic sumcheck.
    pub(super) sums: Option<[F; 3]>,
}

impl<'a, F: PrimeField, MM: MarlinMode> ProverState<'a, F, MM> {
    pub fn initialize(
        padded_public_input: Vec<F>,
        private_variables: Vec<F>,
        zk_bound: usize,
        index: &'a Circuit<F, MM>,
    ) -> Result<Self, AHPError> {
        let index_info = &index.index_info;
        let constraint_domain =
            EvaluationDomain::new(index_info.num_constraints).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let non_zero_a_domain =
            EvaluationDomain::new(index_info.num_non_zero_a).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let non_zero_b_domain =
            EvaluationDomain::new(index_info.num_non_zero_b).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let non_zero_c_domain =
            EvaluationDomain::new(index_info.num_non_zero_c).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let input_domain =
            EvaluationDomain::new(padded_public_input.len()).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        Ok(Self {
            padded_public_variables: padded_public_input,
            private_variables,
            zk_bound,
            index,
            input_domain,
            constraint_domain,
            non_zero_a_domain,
            non_zero_b_domain,
            non_zero_c_domain,
            mask_poly: None,
            verifier_first_message: None,
            w_poly: None,
            mz_poly_randomizer: None,
            mz_polys: None,
            z_a: None,
            z_b: None,
            lhs_polynomials: None,
            sums: None,
        })
    }

    /// Get the public input.
    pub fn public_input(&self) -> Vec<F> {
        ProverConstraintSystem::unformat_public_input(&self.padded_public_variables)
    }

    /// Get the padded public input.
    pub fn padded_public_input(&self) -> &[F] {
        &self.padded_public_variables
    }
}
