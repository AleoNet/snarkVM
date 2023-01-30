// Copyright (C) 2019-2022 Aleo Systems Inc.
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

use std::{collections::BTreeMap, sync::Arc};

use crate::{
    fft::{
        domain::{FFTPrecomputation, IFFTPrecomputation},
        DensePolynomial,
        EvaluationDomain,
        Evaluations as EvaluationsOnDomain,
    },
    snark::marlin::{
        ahp::{indexer::Circuit, verifier},
        AHPError,
        MarlinMode,
    },
};
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{SynthesisError, SynthesisResult};

pub struct IndexSpecificState<'a, F: PrimeField> {
    pub(super) input_domain: EvaluationDomain<F>,
    pub(super) constraint_domain: EvaluationDomain<F>,
    pub(super) non_zero_a_domain: EvaluationDomain<F>,
    pub(super) non_zero_b_domain: EvaluationDomain<F>,
    pub(super) non_zero_c_domain: EvaluationDomain<F>,

    /// The number of instances being proved in this batch.
    pub(in crate::snark) batch_size: usize,

    /// The list of public inputs for each instance in the batch.
    /// The length of this list must be equal to the batch size.
    pub(super) padded_public_variables: Vec<&'a [F]>,

    /// The list of private variables for each instance in the batch.
    /// The length of this list must be equal to the batch size.
    pub(super) private_variables: Vec<&'a [F]>,

    /// The list of Az vectors for each instance in the batch.
    /// The length of this list must be equal to the batch size.
    pub(super) z_a: Option<Vec<Vec<F>>>,

    /// The list of Bz vectors for each instance in the batch.
    /// The length of this list must be equal to the batch size.
    pub(super) z_b: Option<Vec<Vec<F>>>,

    /// A list of polynomials corresponding to the interpolation of the public input.
    /// The length of this list must be equal to the batch size.
    pub(super) x_polys: Vec<DensePolynomial<F>>,

    /// Randomizers for z_b.
    /// The length of this list must be equal to the batch size.
    pub(super) mz_poly_randomizer: Option<Vec<F>>,

    /// The challenges sent by the verifier in the first round
    pub(super) verifier_first_message: Option<verifier::FirstMessage<F>>,

    /// Polynomials involved in the holographic sumcheck.
    pub(super) lhs_polynomials: Option<[DensePolynomial<F>; 3]>,
    /// Polynomials involved in the holographic sumcheck.
    pub(super) sums: Option<[F; 3]>,
}

/// State for the AHP prover.
pub struct State<'a, F: PrimeField, MM: MarlinMode> {
    pub(super) index_specific_states: BTreeMap<&'a Circuit<F, MM>, IndexSpecificState<'a, F>>,
    /// The first round oracles sent by the prover.
    /// The length of this list must be equal to the batch size.
    pub(in crate::snark) first_round_oracles: Option<Arc<super::FirstOracles<'a, F, MM>>>,
}

type PaddedPubInputs<F> = Vec<F>;
type PrivateInputs<F> = Vec<F>;
impl<'a, F: PrimeField, MM: MarlinMode> State<'a, F, MM> {
    pub fn initialize(
        // TODO: which map should we use?
        // IndexMap or BTreeMap?
        indices_and_assignments: BTreeMap<&'a Circuit<F, MM>, Vec<(PaddedPubInputs<F>, PrivateInputs<F>)>>,
    ) -> Result<Self, AHPError> {
        let index_specific_states = indices_and_assignments
            .iter()
            .map(|(circuit, variable_assignments)| {
                let index_info = &circuit.index_info;
                let constraint_domain = EvaluationDomain::new(index_info.num_constraints)
                    .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

                let non_zero_a_domain =
                    EvaluationDomain::new(index_info.num_non_zero_a).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
                let non_zero_b_domain =
                    EvaluationDomain::new(index_info.num_non_zero_b).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
                let non_zero_c_domain =
                    EvaluationDomain::new(index_info.num_non_zero_c).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

                let mut input_domain = None;
                let (x_polys, variables): (Vec<_>, Vec<_>) = variable_assignments.iter().map(|(padded_public_input, private_variable)| {
                    input_domain = input_domain.or_else(|| EvaluationDomain::new(padded_public_input.len()));
                    let x_poly = EvaluationsOnDomain::from_vec_and_domain(padded_public_input.clone(), input_domain.unwrap())
                            .interpolate();
                    (x_poly, (padded_public_input.as_slice(), private_variable.as_slice()))
                }).unzip();
                let input_domain = input_domain.unwrap();
                let (padded_public_variables, private_variables): (Vec<_>, Vec<_>) = variables.into_iter().unzip();

                let batch_size = x_polys.len();
                let state = IndexSpecificState {
                    input_domain,
                    constraint_domain,
                    non_zero_a_domain,
                    non_zero_b_domain,
                    non_zero_c_domain,
                    batch_size,
                    padded_public_variables,
                    x_polys,
                    private_variables,
                    z_a: None,
                    z_b: None,
                    mz_poly_randomizer: None,
                    verifier_first_message: None,
                    lhs_polynomials: None,
                    sums: None,
                };
                Ok((*circuit, state))
            })
            .collect::<SynthesisResult<BTreeMap<_, _>>>()?;

        Ok(Self {
            index_specific_states,
            first_round_oracles: None,
        })
    }

    /// Get the batch size.
    pub fn batch_size(&self, circuit: &Circuit<F, MM>) -> Option<usize> {
        self.index_specific_states.get(circuit).map(|s| s.batch_size)
    }

    /// Get the public inputs for the entire batch.
    pub fn public_inputs(&self, circuit: &Circuit<F, MM>) -> Option<Vec<Vec<F>>> {
        self.index_specific_states.get(circuit).map(|s| s.padded_public_variables.iter().map(|v| super::ConstraintSystem::unformat_public_input(v)).collect())
    }

    /// Get the padded public inputs for the entire batch.
    pub fn padded_public_inputs(&self, circuit: &Circuit<F, MM>) -> Option<&[&[F]]> {
        self.index_specific_states.get(circuit).map(|s| s.padded_public_variables.as_slice())
    }

    pub fn fft_precomputation(&self, circuit: &Circuit<F, MM>) -> Option<&FFTPrecomputation<F>> {
        self.index_specific_states.contains_key(circuit).then(|| &circuit.fft_precomputation)
    }

    pub fn ifft_precomputation(&self, circuit: &Circuit<F, MM>) -> Option<&IFFTPrecomputation<F>> {
        self.index_specific_states.contains_key(circuit).then(|| &circuit.ifft_precomputation)
    }
}
