// Copyright (C) 2019-2023 Aleo Systems Inc.
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
    fft::{DensePolynomial, EvaluationDomain, Evaluations as EvaluationsOnDomain},
    snark::marlin::{ahp::verifier, AHPError, AHPForR1CS, Circuit, MarlinMode},
};
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::SynthesisResult;

/// Circuit Specific State of the Prover
pub struct CircuitSpecificState<F: PrimeField> {
    pub(super) input_domain: EvaluationDomain<F>,
    pub(super) constraint_domain: EvaluationDomain<F>,
    pub(super) non_zero_a_domain: EvaluationDomain<F>,
    pub(super) non_zero_b_domain: EvaluationDomain<F>,
    pub(super) non_zero_c_domain: EvaluationDomain<F>,

    /// The number of instances being proved in this batch.
    pub(in crate::snark) batch_size: usize,

    /// The list of public inputs for each instance in the batch.
    /// The length of this list must be equal to the batch size.
    pub(super) padded_public_variables: Vec<Vec<F>>,

    /// The list of private variables for each instance in the batch.
    /// The length of this list must be equal to the batch size.
    pub(super) private_variables: Vec<Vec<F>>,

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

    /// Polynomials involved in the holographic sumcheck.
    pub(super) lhs_polynomials: Option<[DensePolynomial<F>; 3]>,
}

/// State for the AHP prover.
pub struct State<'a, F: PrimeField, MM: MarlinMode> {
    /// The state for each circuit in the batch.
    pub(super) circuit_specific_states: BTreeMap<&'a Circuit<F, MM>, CircuitSpecificState<F>>,
    /// The challenges sent by the verifier in the first round.
    pub(super) verifier_first_message: Option<verifier::FirstMessage<F>>,
    /// The first round oracles sent by the prover.
    /// The length of this list must be equal to the batch size.
    pub(in crate::snark) first_round_oracles: Option<Arc<super::FirstOracles<F>>>,
    /// The largest non_zero domain of all circuits in the batch.
    pub(in crate::snark) max_non_zero_domain: EvaluationDomain<F>,
    /// The largest constraint domain of all circuits in the batch.
    pub(in crate::snark) max_constraint_domain: EvaluationDomain<F>,
    /// The total number of instances we're proving in the batch.
    pub(in crate::snark) total_instances: usize,
}

/// The public inputs for a single instance.
type PaddedPubInputs<F> = Vec<F>;
/// The private inputs for a single instance.
type PrivateInputs<F> = Vec<F>;
/// The z_i_j*A_i vector for a single instance.
type Za<F> = Vec<F>;
/// The z_i_j*B_i vector for a single instance.
type Zb<F> = Vec<F>;
/// Assignments for a single instance.
pub(super) struct Assignments<F>(
    pub(super) PaddedPubInputs<F>,
    pub(super) PrivateInputs<F>,
    pub(super) Za<F>,
    pub(super) Zb<F>,
);

impl<'a, F: PrimeField, MM: MarlinMode> State<'a, F, MM> {
    pub(super) fn initialize(
        indices_and_assignments: BTreeMap<&'a Circuit<F, MM>, Vec<Assignments<F>>>,
    ) -> Result<Self, AHPError> {
        let mut max_constraint_domain: Option<EvaluationDomain<F>> = None;
        let mut max_non_zero_domain: Option<EvaluationDomain<F>> = None;
        let mut total_instances = 0;
        let circuit_specific_states = indices_and_assignments
            .into_iter()
            .map(|(circuit, variable_assignments)| {
                let index_info = &circuit.index_info;
                let constraint_domains = AHPForR1CS::<_, MM>::max_constraint_domain(index_info, max_constraint_domain)?;
                max_constraint_domain = constraint_domains.max_constraint_domain;

                let non_zero_domains = AHPForR1CS::<_, MM>::max_non_zero_domain(index_info, max_non_zero_domain)?;
                max_non_zero_domain = non_zero_domains.max_non_zero_domain;

                let first_padded_public_inputs = &variable_assignments[0].0;
                let input_domain = EvaluationDomain::new(first_padded_public_inputs.len()).unwrap();
                let batch_size = variable_assignments.len();
                total_instances += batch_size;
                let mut z_as = Vec::with_capacity(batch_size);
                let mut z_bs = Vec::with_capacity(batch_size);
                let mut x_polys = Vec::with_capacity(batch_size);
                let mut padded_public_variables = Vec::with_capacity(batch_size);
                let mut private_variables = Vec::with_capacity(batch_size);

                for Assignments(padded_public_input, private_input, z_a, z_b) in variable_assignments {
                    z_as.push(z_a);
                    z_bs.push(z_b);
                    let x_poly = EvaluationsOnDomain::from_vec_and_domain(padded_public_input.clone(), input_domain)
                        .interpolate();
                    x_polys.push(x_poly);
                    padded_public_variables.push(padded_public_input);
                    private_variables.push(private_input);
                }

                let state = CircuitSpecificState {
                    input_domain,
                    constraint_domain: constraint_domains.constraint_domain,
                    non_zero_a_domain: non_zero_domains.domain_a,
                    non_zero_b_domain: non_zero_domains.domain_b,
                    non_zero_c_domain: non_zero_domains.domain_c,
                    batch_size,
                    padded_public_variables,
                    x_polys,
                    private_variables,
                    z_a: Some(z_as),
                    z_b: Some(z_bs),
                    mz_poly_randomizer: None,
                    lhs_polynomials: None,
                };
                Ok((circuit, state))
            })
            .collect::<SynthesisResult<BTreeMap<_, _>>>()?;

        let max_constraint_domain = max_constraint_domain.ok_or(AHPError::BatchSizeIsZero)?;
        let max_non_zero_domain = max_non_zero_domain.ok_or(AHPError::BatchSizeIsZero)?;

        Ok(Self {
            max_constraint_domain,
            max_non_zero_domain,
            circuit_specific_states,
            total_instances,
            first_round_oracles: None,
            verifier_first_message: None,
        })
    }

    /// Get the batch size for a given circuit.
    pub fn batch_size(&self, circuit: &Circuit<F, MM>) -> Option<usize> {
        self.circuit_specific_states.get(circuit).map(|s| s.batch_size)
    }

    /// Get the public inputs for the entire batch.
    pub fn public_inputs(&self, circuit: &Circuit<F, MM>) -> Option<Vec<Vec<F>>> {
        // We need to export inputs as they live longer than prover_state
        self.circuit_specific_states.get(circuit).map(|s| {
            s.padded_public_variables.iter().map(|v| super::ConstraintSystem::unformat_public_input(v)).collect()
        })
    }

    /// Get the padded public inputs for the entire batch.
    pub fn padded_public_inputs(&self, circuit: &Circuit<F, MM>) -> Option<&[Vec<F>]> {
        self.circuit_specific_states.get(circuit).map(|s| s.padded_public_variables.as_slice())
    }

    /// Iterate over the lhs_polynomials
    pub fn lhs_polys_into_iter(self) -> impl Iterator<Item = DensePolynomial<F>> + 'a {
        self.circuit_specific_states.into_values().flat_map(|s| s.lhs_polynomials.unwrap().into_iter())
    }
}
