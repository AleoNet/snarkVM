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
    ahp::{indexer::Circuit, prover::ProverConstraintSystem, verifier::VerifierFirstMessage},
    Vec,
};
use snarkvm_algorithms::fft::EvaluationDomain;
use snarkvm_curves::traits::PrimeField;
use snarkvm_polycommit::LabeledPolynomial;

/// State for the AHP prover.
pub struct ProverState<'a, F: PrimeField> {
    pub(crate) padded_public_variables: Vec<F>,
    pub(crate) private_variables: Vec<F>,
    /// Az
    pub(crate) z_a: Option<Vec<F>>,
    /// Bz
    pub(crate) z_b: Option<Vec<F>>,
    /// query bound b
    pub(crate) zk_bound: usize,

    pub(crate) w_poly: Option<LabeledPolynomial<F>>,
    pub(crate) mz_polys: Option<(LabeledPolynomial<F>, LabeledPolynomial<F>)>,

    pub(crate) index: &'a Circuit<F>,

    /// the random values sent by the verifier in the first round
    pub(crate) verifier_first_message: Option<VerifierFirstMessage<F>>,

    /// the blinding polynomial for the first round
    pub(crate) mask_poly: Option<LabeledPolynomial<F>>,

    /// domain X, sized for the public input
    pub(crate) domain_x: EvaluationDomain<F>,

    /// domain H, sized for constraints
    pub(crate) domain_h: EvaluationDomain<F>,

    /// domain K, sized for matrix nonzero elements
    pub(crate) domain_k: EvaluationDomain<F>,
}

impl<'a, F: PrimeField> ProverState<'a, F> {
    /// Get the public input.
    pub fn public_input(&self) -> Vec<F> {
        ProverConstraintSystem::unformat_public_input(&self.padded_public_variables)
    }
}
