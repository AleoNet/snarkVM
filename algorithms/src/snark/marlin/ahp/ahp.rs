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

use crate::{
    fft::{
        domain::{FFTPrecomputation, IFFTPrecomputation},
        EvaluationDomain,
    },
    polycommit::sonic_pc::{LCTerm, LabeledPolynomial, LinearCombination},
    snark::marlin::{
        ahp::{matrices, verifier, AHPError, CircuitId, CircuitInfo},
        prover,
        MarlinMode,
    },
};
use itertools::Itertools;
use snarkvm_fields::{Field, PrimeField};
use snarkvm_r1cs::SynthesisError;

use core::{borrow::Borrow, marker::PhantomData};
use std::collections::BTreeMap;

/// The algebraic holographic proof defined in [CHMMVW19](https://eprint.iacr.org/2019/1047).
/// Currently, this AHP only supports inputs of size one
/// less than a power of 2 (i.e., of the form 2^n - 1).
pub struct AHPForR1CS<F: Field, MM: MarlinMode> {
    field: PhantomData<F>,
    mode: PhantomData<MM>,
}

#[derive(Debug, Clone, Copy)]
struct VerifierChallenges<F: Field> {
    alpha: F,
    beta: F,
    gamma: F,
}

pub(crate) fn witness_label(circuit_id: CircuitId, poly: &str, i: usize) -> String {
    format!("circuit_{circuit_id}_{poly}_{i:0>8}")
}

pub(crate) struct ConstraintDomains<F: PrimeField> {
    pub(crate) max_constraint_domain: Option<EvaluationDomain<F>>,
    pub(crate) constraint_domain: EvaluationDomain<F>,
}

pub(crate) struct NonZeroDomains<F: PrimeField> {
    pub(crate) max_non_zero_domain: Option<EvaluationDomain<F>>,
    pub(crate) domain_a: EvaluationDomain<F>,
    pub(crate) domain_b: EvaluationDomain<F>,
    pub(crate) domain_c: EvaluationDomain<F>,
}

impl<F: PrimeField, MM: MarlinMode> AHPForR1CS<F, MM> {
    /// The linear combinations that are statically known to evaluate to zero.
    /// These correspond to the virtual commitments as noted in the Aleo marlin protocol docs
    #[rustfmt::skip]
    pub const LC_WITH_ZERO_EVAL: [&'static str; 2] = ["matrix_sumcheck", "lincheck_sumcheck"];

    pub fn zk_bound() -> Option<usize> {
        MM::ZK.then_some(1)
    }

    /// Check that the (formatted) public input is of the form 2^n for some integer n.
    pub fn num_formatted_public_inputs_is_admissible(num_inputs: usize) -> Result<(), AHPError> {
        match num_inputs.count_ones() == 1 {
            true => Ok(()),
            false => Err(AHPError::InvalidPublicInputLength),
        }
    }

    /// Check that the (formatted) public input is of the form 2^n for some integer n.
    pub fn formatted_public_input_is_admissible(input: &[F]) -> Result<(), AHPError> {
        Self::num_formatted_public_inputs_is_admissible(input.len())
    }

    /// The maximum degree of polynomials produced by the indexer and prover
    /// of this protocol.
    /// The number of the variables must include the "one" variable. That is, it
    /// must be with respect to the number of formatted public inputs.
    pub fn max_degree(num_constraints: usize, num_variables: usize, num_non_zero: usize) -> Result<usize, AHPError> {
        let padded_matrix_dim = matrices::padded_matrix_dim(num_variables, num_constraints);
        let zk_bound = Self::zk_bound().unwrap_or(0);
        let constraint_domain_size = EvaluationDomain::<F>::compute_size_of_domain(padded_matrix_dim)
            .ok_or(AHPError::PolynomialDegreeTooLarge)?;
        let non_zero_domain_size =
            EvaluationDomain::<F>::compute_size_of_domain(num_non_zero).ok_or(AHPError::PolynomialDegreeTooLarge)?;

        Ok(*[
            2 * constraint_domain_size + zk_bound - 2,
            if MM::ZK { constraint_domain_size + 3 } else { 0 }, //  mask_poly
            constraint_domain_size,
            constraint_domain_size,
            non_zero_domain_size - 1, // non-zero polynomials
        ]
        .iter()
        .max()
        .unwrap())
    }

    /// Get all the strict degree bounds enforced in the AHP.
    pub fn get_degree_bounds(info: &CircuitInfo<F>) -> [usize; 4] {
        let num_constraints = info.num_constraints;
        let num_non_zero_a = info.num_non_zero_a;
        let num_non_zero_b = info.num_non_zero_b;
        let num_non_zero_c = info.num_non_zero_c;
        [
            EvaluationDomain::<F>::compute_size_of_domain(num_constraints).unwrap() - 2,
            EvaluationDomain::<F>::compute_size_of_domain(num_non_zero_a).unwrap() - 2,
            EvaluationDomain::<F>::compute_size_of_domain(num_non_zero_b).unwrap() - 2,
            EvaluationDomain::<F>::compute_size_of_domain(num_non_zero_c).unwrap() - 2,
        ]
    }

    pub(crate) fn max_constraint_domain(
        info: &CircuitInfo<F>,
        max_candidate: Option<EvaluationDomain<F>>,
    ) -> Result<ConstraintDomains<F>, SynthesisError> {
        let constraint_domain =
            EvaluationDomain::new(info.num_constraints).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let mut max_constraint_domain = Some(constraint_domain);
        if max_candidate.is_some() && max_candidate.unwrap().size() > constraint_domain.size() {
            max_constraint_domain = max_candidate;
        }
        Ok(ConstraintDomains { max_constraint_domain, constraint_domain })
    }

    pub(crate) fn max_non_zero_domain(
        info: &CircuitInfo<F>,
        max_candidate: Option<EvaluationDomain<F>>,
    ) -> Result<NonZeroDomains<F>, SynthesisError> {
        let domain_a = EvaluationDomain::new(info.num_non_zero_a).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let domain_b = EvaluationDomain::new(info.num_non_zero_b).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let domain_c = EvaluationDomain::new(info.num_non_zero_c).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let new_candidate = [domain_a, domain_b, domain_c].into_iter().max_by_key(|d| d.size()).unwrap();
        let mut max_non_zero_domain = Some(new_candidate);
        if max_candidate.is_some() && max_candidate.unwrap().size() > new_candidate.size() {
            max_non_zero_domain = max_candidate;
        }
        Ok(NonZeroDomains { max_non_zero_domain, domain_a, domain_b, domain_c })
    }

    pub fn fft_precomputation(
        constraint_domain_size: usize,
        non_zero_a_domain_size: usize,
        non_zero_b_domain_size: usize,
        non_zero_c_domain_size: usize,
    ) -> Option<(FFTPrecomputation<F>, IFFTPrecomputation<F>)> {
        let largest_domain_size = [
            3 * constraint_domain_size,
            non_zero_a_domain_size * 2,
            non_zero_b_domain_size * 2,
            non_zero_c_domain_size * 2,
        ]
        .into_iter()
        .max()?;
        let largest_mul_domain = EvaluationDomain::new(largest_domain_size)?;

        let fft_precomputation = largest_mul_domain.precompute_fft();
        let ifft_precomputation = fft_precomputation.to_ifft_precomputation();
        Some((fft_precomputation, ifft_precomputation))
    }

    /// Construct the linear combinations that are checked by the AHP.
    /// Public input should be unformatted.
    /// We construct the linear combinations as per section 5 of our protocol documentation.
    /// We can distinguish between:
    /// (1) simple comitments: $\{\cm{g_A}, \cm{g_B}, \cm{g_C}\}$ and $\{\cm{\hat{z}_{B,i,j}}\}_{i \in {[\mathcal{D}]}}$, $\cm{g_1}$
    /// (2) virtual commitments for the lincheck_sumcheck and matrix_sumcheck. These are linear combinations of the simple commitments
    #[allow(non_snake_case)]
    pub fn construct_linear_combinations<E: EvaluationsProvider<F>>(
        public_inputs: &BTreeMap<CircuitId, Vec<Vec<F>>>,
        evals: &E,
        prover_third_message: &prover::ThirdMessage<F>,
        state: &verifier::State<F, MM>,
    ) -> Result<BTreeMap<String, LinearCombination<F>>, AHPError> {
        assert!(!public_inputs.is_empty());
        let largest_constraint_domain = state.max_constraint_domain;
        let max_non_zero_domain = state.largest_non_zero_domain;
        let public_inputs = state
            .circuit_specific_states
            .iter()
            .map(|(circuit_id, circuit_state)| {
                let input_domain = circuit_state.input_domain;
                let public_inputs = public_inputs[circuit_id]
                    .iter()
                    .map(|p| {
                        let public_input = prover::ConstraintSystem::format_public_input(p);
                        Self::formatted_public_input_is_admissible(&public_input).map(|_| public_input)
                    })
                    .collect::<Result<Vec<_>, _>>();
                assert_eq!(public_inputs.as_ref().unwrap()[0].len(), input_domain.size());
                public_inputs
            })
            .collect::<Result<Vec<_>, _>>()?;

        let first_round_msg = state.first_round_message.as_ref().unwrap();
        let alpha = first_round_msg.alpha;
        let eta_a = F::one();
        let eta_b = first_round_msg.eta_b;
        let eta_c = first_round_msg.eta_c;
        let batch_combiners = &first_round_msg.batch_combiners;
        let prover::ThirdMessage { sums } = prover_third_message;

        let t_at_beta_s = state
            .circuit_specific_states
            .iter()
            .enumerate()
            .map(|(i, (circuit_id, circuit_state))| {
                let sums_i = &sums[i];
                let t_at_beta = eta_a * circuit_state.non_zero_a_domain.size_as_field_element * sums_i.sum_a
                    + eta_b * circuit_state.non_zero_b_domain.size_as_field_element * sums_i.sum_b
                    + eta_c * circuit_state.non_zero_c_domain.size_as_field_element * sums_i.sum_c;
                (circuit_id, t_at_beta)
            })
            .collect::<BTreeMap<_, _>>();

        let verifier::ThirdMessage { delta_a, delta_b, delta_c } = state.third_round_message.as_ref().unwrap();
        let beta = state.second_round_message.unwrap().beta;
        let gamma = state.gamma.unwrap();

        let mut linear_combinations = BTreeMap::new();
        let mut selectors = BTreeMap::new();

        // Lincheck sumcheck:
        let lincheck_time = start_timer!(|| "Lincheck");
        let z_b_s = state
            .circuit_specific_states
            .iter()
            .map(|(&circuit_id, circuit_state)| {
                let z_b_i = (0..circuit_state.batch_size)
                    .map(|i| {
                        let z_b = witness_label(circuit_id, "z_b", i);
                        LinearCombination::new(z_b.clone(), [(F::one(), z_b)])
                    })
                    .collect::<Vec<_>>();
                (circuit_id, z_b_i)
            })
            .collect::<BTreeMap<_, _>>();

        let g_1 = LinearCombination::new("g_1", [(F::one(), "g_1")]);

        let bivariate_poly_time = start_timer!(|| "Bivariate poly");
        let mut r_alpha_at_beta_s = BTreeMap::new();
        for (circuit_id, circuit_state) in state.circuit_specific_states.iter() {
            r_alpha_at_beta_s.insert(
                circuit_id,
                circuit_state.constraint_domain.eval_unnormalized_bivariate_lagrange_poly(alpha, beta),
            );
        }
        end_timer!(bivariate_poly_time);

        let v_H_at_beta_time = start_timer!(|| "v_H_at_beta");
        let v_H_at_beta = largest_constraint_domain.evaluate_vanishing_polynomial(beta);
        end_timer!(v_H_at_beta_time);

        let v_X_at_beta_time = start_timer!(|| "v_X_at_beta");
        let v_X_at_beta = state
            .circuit_specific_states
            .iter()
            .map(|(circuit_id, circuit_state)| {
                let v_X_i_at_beta = circuit_state.input_domain.evaluate_vanishing_polynomial(beta);
                (circuit_id, v_X_i_at_beta)
            })
            .collect::<BTreeMap<_, _>>();
        end_timer!(v_X_at_beta_time);

        let z_b_s_at_beta = z_b_s
            .iter()
            .map(|(circuit_id, z_b_i)| {
                let z_b_i_s = z_b_i.iter().map(|z_b| evals.get_lc_eval(z_b, beta).unwrap()).collect::<Vec<F>>();
                (*circuit_id, z_b_i_s)
            })
            .collect::<BTreeMap<_, _>>();
        let batch_z_b_s_at_beta = z_b_s_at_beta
            .iter()
            .zip_eq(batch_combiners.values())
            .zip_eq(r_alpha_at_beta_s.values())
            .map(|(((circuit_id, z_b_i_at_beta), combiners), &r_alpha_at_beta)| {
                let z_b_at_beta = z_b_i_at_beta
                    .iter()
                    .zip_eq(&combiners.instance_combiners)
                    .map(|(z_b_at_beta, instance_combiner)| *z_b_at_beta * instance_combiner)
                    .sum::<F>();
                (*circuit_id, r_alpha_at_beta * z_b_at_beta)
            })
            .collect::<BTreeMap<_, _>>();
        let g_1_at_beta = evals.get_lc_eval(&g_1, beta)?;

        let combined_x_at_betas = state
            .circuit_specific_states
            .iter()
            .enumerate()
            .map(|(i, (circuit_id, circuit_state))| {
                let lag_at_beta = circuit_state.input_domain.evaluate_all_lagrange_coefficients(beta);
                let combined_x_at_beta = batch_combiners[circuit_id]
                    .instance_combiners
                    .iter()
                    .zip_eq(public_inputs[i].iter())
                    .map(|(c, x)| x.iter().zip_eq(&lag_at_beta).map(|(x, l)| *x * l).sum::<F>() * c)
                    .sum::<F>();
                (circuit_id, combined_x_at_beta)
            })
            .collect::<BTreeMap<_, _>>();

        // We're now going to calculate the lincheck_sumcheck
        // Note that we precalculated a number of terms already to prevent duplicate calculations:
        #[rustfmt::skip]
        let lincheck_sumcheck = {
            let mut lincheck_sumcheck = LinearCombination::empty("lincheck_sumcheck");
            if MM::ZK {
                lincheck_sumcheck.add(F::one(), "mask_poly");
            }
            for (id, c) in batch_combiners.iter() {
                let mut circuit_term = LinearCombination::empty(format!("lincheck_sumcheck term {id}"));
                for (j, instance_combiner) in c.instance_combiners.iter().enumerate() {
                    let z_a_j = witness_label(*id, "z_a", j);
                    let w_j = witness_label(*id, "w", j);
                    circuit_term
                        .add(r_alpha_at_beta_s[id] * instance_combiner * (eta_a + eta_c * z_b_s_at_beta[id][j]), z_a_j)
                        .add(-t_at_beta_s[id] * v_X_at_beta[id] * instance_combiner, w_j);
                }
               circuit_term
                    .add(-t_at_beta_s[id] * combined_x_at_betas[id], LCTerm::One)
                    .add(eta_b * batch_z_b_s_at_beta[id], LCTerm::One);
                let constraint_domain = state.circuit_specific_states[id].constraint_domain;
                let selector = selector_evals(&mut selectors, &largest_constraint_domain, &constraint_domain, beta);
                circuit_term *= selector;
                lincheck_sumcheck += (c.circuit_combiner, &circuit_term);
            }
            lincheck_sumcheck
                .add(-v_H_at_beta, "h_1")
                .add(-beta * g_1_at_beta, LCTerm::One);
            lincheck_sumcheck
        };
        debug_assert!(evals.get_lc_eval(&lincheck_sumcheck, beta)?.is_zero());

        for z_b in z_b_s.into_values() {
            for z_b_i in z_b {
                linear_combinations.insert(z_b_i.label.clone(), z_b_i);
            }
        }
        linear_combinations.insert("g_1".into(), g_1);
        linear_combinations.insert("lincheck_sumcheck".into(), lincheck_sumcheck);
        end_timer!(lincheck_time);

        //  Matrix sumcheck:
        let mut matrix_sumcheck = LinearCombination::empty("matrix_sumcheck");

        for (i, (&id, circuit_state)) in state.circuit_specific_states.iter().enumerate() {
            let v_H_i_at_alpha_time = start_timer!(|| format!("v_H_i_at_alpha {id}"));
            let v_H_i_at_alpha = circuit_state.constraint_domain.evaluate_vanishing_polynomial(alpha);
            end_timer!(v_H_i_at_alpha_time);

            let v_H_i_at_beta_time = start_timer!(|| format!("v_H_i_at_beta {id}"));
            let v_H_i_at_beta = circuit_state.constraint_domain.evaluate_vanishing_polynomial(beta);
            end_timer!(v_H_i_at_beta_time);
            let v_H_i = v_H_i_at_alpha * v_H_i_at_beta;

            let s_a = selector_evals(&mut selectors, &max_non_zero_domain, &circuit_state.non_zero_a_domain, gamma);
            let s_b = selector_evals(&mut selectors, &max_non_zero_domain, &circuit_state.non_zero_b_domain, gamma);
            let s_c = selector_evals(&mut selectors, &max_non_zero_domain, &circuit_state.non_zero_c_domain, gamma);

            let g_a_label = witness_label(id, "g_a", 0);
            let g_a = LinearCombination::new(g_a_label.clone(), [(F::one(), g_a_label)]);
            let g_b_label = witness_label(id, "g_b", 0);
            let g_b = LinearCombination::new(g_b_label.clone(), [(F::one(), g_b_label)]);
            let g_c_label = witness_label(id, "g_c", 0);
            let g_c = LinearCombination::new(g_c_label.clone(), [(F::one(), g_c_label)]);

            let challenges = VerifierChallenges { alpha, beta, gamma };
            let sum_a = sums[i].sum_a;
            let sum_b = sums[i].sum_b;
            let sum_c = sums[i].sum_c;

            Self::add_g_m_term(&mut matrix_sumcheck, id, "a", challenges, evals, &g_a, v_H_i, delta_a[i], sum_a, s_a)?;
            Self::add_g_m_term(&mut matrix_sumcheck, id, "b", challenges, evals, &g_b, v_H_i, delta_b[i], sum_b, s_b)?;
            Self::add_g_m_term(&mut matrix_sumcheck, id, "c", challenges, evals, &g_c, v_H_i, delta_c[i], sum_c, s_c)?;

            linear_combinations.insert(g_a.label.clone(), g_a);
            linear_combinations.insert(g_b.label.clone(), g_b);
            linear_combinations.insert(g_c.label.clone(), g_c);
        }

        matrix_sumcheck -=
            &LinearCombination::new("h_2", [(max_non_zero_domain.evaluate_vanishing_polynomial(gamma), "h_2")]);
        debug_assert!(evals.get_lc_eval(&matrix_sumcheck, gamma)?.is_zero());

        linear_combinations.insert("matrix_sumcheck".into(), matrix_sumcheck);

        Ok(linear_combinations)
    }

    #[allow(clippy::too_many_arguments)]
    fn add_g_m_term<E: EvaluationsProvider<F>>(
        matrix_sumcheck: &mut LinearCombination<F>,
        id: CircuitId,
        m: &str,
        challenges: VerifierChallenges<F>,
        evals: &E,
        g_m: &LinearCombination<F>,
        v_h_i_alpha_beta: F,
        r: F,
        sum: F,
        selector: F,
    ) -> Result<(), AHPError> {
        let g_at_gamma = evals.get_lc_eval(g_m, challenges.gamma)?;
        let b_term = challenges.gamma * g_at_gamma + sum; // Xg_m(X) + sum_m
        let lhs_a = Self::construct_lhs(id, m, challenges.alpha, challenges.beta, v_h_i_alpha_beta, b_term, selector);
        *matrix_sumcheck += (r, &lhs_a);
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn construct_lhs(
        id: CircuitId,
        label: &str,
        alpha: F,
        beta: F,
        v_h_i_at_alpha_beta: F,
        b_term: F,
        selector_at_gamma: F,
    ) -> LinearCombination<F> {
        let label_row = format!("circuit_{id}_row_{label}");
        let label_col = format!("circuit_{id}_col_{label}");
        let label_val = format!("circuit_{id}_val_{label}");
        let label_row_col = format!("circuit_{id}_row_col_{label}");
        let label_a_poly = format!("circuit_{id}_a_poly_{label}");
        let label_denom = format!("circuit_{id}_denom_{label}");

        let a = LinearCombination::new(label_a_poly, [(v_h_i_at_alpha_beta, label_val)]);
        let alpha_beta = alpha * beta;

        let mut b = LinearCombination::new(label_denom, [
            (alpha_beta, LCTerm::One),
            (-alpha, (label_row).into()),
            (-beta, (label_col).into()),
            (F::one(), (label_row_col).into()),
        ]);
        b *= b_term; // Xg_m(X) + sum_m

        let mut lhs = a;
        lhs -= &b;
        lhs *= selector_at_gamma;
        lhs
    }
}

fn selector_evals<F: PrimeField>(
    cached_selector_evaluations: &mut BTreeMap<(u64, u64, F), F>,
    largest_domain: &EvaluationDomain<F>,
    target_domain: &EvaluationDomain<F>,
    challenge: F,
) -> F {
    *cached_selector_evaluations
        .entry((target_domain.size, largest_domain.size, challenge))
        .or_insert_with(|| largest_domain.evaluate_selector_polynomial(*target_domain, challenge))
}

/// Abstraction that provides evaluations of (linear combinations of) polynomials
///
/// Intended to provide a common interface for both the prover and the verifier
/// when constructing linear combinations via `AHPForR1CS::construct_linear_combinations`.
pub trait EvaluationsProvider<F: PrimeField>: core::fmt::Debug {
    /// Get the evaluation of linear combination `lc` at `point`.
    fn get_lc_eval(&self, lc: &LinearCombination<F>, point: F) -> Result<F, AHPError>;
}

impl<F: PrimeField> EvaluationsProvider<F> for crate::polycommit::sonic_pc::Evaluations<F> {
    fn get_lc_eval(&self, lc: &LinearCombination<F>, point: F) -> Result<F, AHPError> {
        let key = (lc.label.clone(), point);
        self.get(&key).copied().ok_or_else(|| AHPError::MissingEval(lc.label.clone()))
    }
}

impl<F, T> EvaluationsProvider<F> for Vec<T>
where
    F: PrimeField,
    T: Borrow<LabeledPolynomial<F>> + core::fmt::Debug,
{
    fn get_lc_eval(&self, lc: &LinearCombination<F>, point: F) -> Result<F, AHPError> {
        let mut eval = F::zero();
        for (coeff, term) in lc.iter() {
            let value = if let LCTerm::PolyLabel(label) = term {
                self.iter()
                    .find(|p| (*p).borrow().label() == label)
                    .ok_or_else(|| AHPError::MissingEval(format!("Missing {} for {}", label, lc.label)))?
                    .borrow()
                    .evaluate(point)
            } else {
                assert!(term.is_one());
                F::one()
            };
            eval += &(*coeff * value)
        }
        Ok(eval)
    }
}

/// The derivative of the vanishing polynomial
pub trait UnnormalizedBivariateLagrangePoly<F: PrimeField> {
    /// Evaluate the polynomial
    fn eval_unnormalized_bivariate_lagrange_poly(&self, x: F, y: F) -> F;

    /// Evaluate over a batch of inputs
    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(&self, x: F) -> Vec<F>;

    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs_over_domain(
        &self,
        x: F,
        domain: &EvaluationDomain<F>,
    ) -> Vec<F>;

    /// Evaluate the magic polynomial over `self`
    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs(&self) -> Vec<F>;
}

impl<F: PrimeField> UnnormalizedBivariateLagrangePoly<F> for EvaluationDomain<F> {
    fn eval_unnormalized_bivariate_lagrange_poly(&self, x: F, y: F) -> F {
        if x != y {
            (self.evaluate_vanishing_polynomial(x) - self.evaluate_vanishing_polynomial(y)) / (x - y)
        } else {
            self.size_as_field_element * x.pow([(self.size() - 1) as u64])
        }
    }

    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs_over_domain(
        &self,
        x: F,
        domain: &EvaluationDomain<F>,
    ) -> Vec<F> {
        use snarkvm_utilities::{cfg_iter, cfg_iter_mut};

        #[cfg(not(feature = "serial"))]
        use rayon::prelude::*;

        let vanish_x = self.evaluate_vanishing_polynomial(x);
        let elements = domain.elements().collect::<Vec<_>>();

        let mut denoms = cfg_iter!(elements).map(|e| x - e).collect::<Vec<_>>();
        if domain.size() <= self.size() {
            snarkvm_fields::batch_inversion_and_mul(&mut denoms, &vanish_x);
        } else {
            snarkvm_fields::batch_inversion(&mut denoms);
            let ratio = domain.size() / self.size();
            let mut numerators = vec![vanish_x; domain.size()];
            cfg_iter_mut!(numerators).zip_eq(elements).enumerate().for_each(|(i, (n, e))| {
                if i % ratio != 0 {
                    *n -= self.evaluate_vanishing_polynomial(e);
                }
            });
            cfg_iter_mut!(denoms).zip_eq(numerators).for_each(|(d, e)| *d *= e);
        }
        denoms
    }

    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(&self, x: F) -> Vec<F> {
        self.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs_over_domain(x, self)
    }

    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs(&self) -> Vec<F> {
        let mut elems: Vec<F> = self.elements().map(|e| e * self.size_as_field_element).collect();
        elems[1..].reverse();
        elems
    }
}

/// Given two domains H and K such that H \subseteq K,
/// construct polynomial that outputs 0 on all elements in K \ H, but 1 on all elements of H.
pub trait SelectorPolynomial<F: PrimeField> {
    fn evaluate_selector_polynomial(&self, other: EvaluationDomain<F>, point: F) -> F;
}

impl<F: PrimeField> SelectorPolynomial<F> for EvaluationDomain<F> {
    fn evaluate_selector_polynomial(&self, other: EvaluationDomain<F>, point: F) -> F {
        let numerator = self.evaluate_vanishing_polynomial(point) * other.size_as_field_element;
        let denominator = other.evaluate_vanishing_polynomial(point) * self.size_as_field_element;
        numerator / denominator
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fft::{DensePolynomial, Evaluations};
    use snarkvm_curves::bls12_377::fr::Fr;
    use snarkvm_fields::{One, Zero};
    use snarkvm_utilities::rand::{TestRng, Uniform};

    #[test]
    fn domain_unnormalized_bivariate_lagrange_poly() {
        for domain_size in 1..10 {
            let domain = EvaluationDomain::<Fr>::new(1 << domain_size).unwrap();
            let manual: Vec<_> =
                domain.elements().map(|elem| domain.eval_unnormalized_bivariate_lagrange_poly(elem, elem)).collect();
            let fast = domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs();
            assert_eq!(fast, manual);
        }
    }

    #[test]
    fn domain_unnormalized_bivariate_lagrange_poly_diff_inputs() {
        let rng = &mut TestRng::default();
        for domain_size in 1..10 {
            let domain = EvaluationDomain::<Fr>::new(1 << domain_size).unwrap();
            let x = Fr::rand(rng);
            let manual: Vec<_> =
                domain.elements().map(|y| domain.eval_unnormalized_bivariate_lagrange_poly(x, y)).collect();
            let fast = domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(x);
            assert_eq!(fast, manual);
        }
    }

    #[test]
    fn domain_unnormalized_bivariate_lagrange_poly_diff_inputs_over_domain() {
        let rng = &mut TestRng::default();
        for domain_size in 1..10 {
            let domain = EvaluationDomain::<Fr>::new(1 << domain_size).unwrap();
            let x = Fr::rand(rng);
            for other_domain_size in 1..10 {
                let other = EvaluationDomain::<Fr>::new(1 << other_domain_size).unwrap();
                let manual: Vec<_> =
                    other.elements().map(|y| domain.eval_unnormalized_bivariate_lagrange_poly(x, y)).collect();
                let fast =
                    domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs_over_domain(x, &other);
                assert_eq!(fast, manual, "failed for self {domain:?} and other {other:?}");
            }
        }
    }

    #[test]
    fn test_summation() {
        let rng = &mut TestRng::default();
        let size = 1 << 4;
        let domain = EvaluationDomain::<Fr>::new(1 << 4).unwrap();
        let size_as_fe = domain.size_as_field_element;
        let poly = DensePolynomial::rand(size, rng);

        let mut sum: Fr = Fr::zero();
        for eval in domain.elements().map(|e| poly.evaluate(e)) {
            sum += &eval;
        }
        let first = poly.coeffs[0] * size_as_fe;
        let last = *poly.coeffs.last().unwrap() * size_as_fe;
        println!("sum: {sum:?}");
        println!("a_0: {first:?}");
        println!("a_n: {last:?}");
        println!("first + last: {:?}\n", first + last);
        assert_eq!(sum, first + last);
    }

    #[test]
    fn test_alternator_polynomial() {
        let mut rng = TestRng::default();

        for i in 1..10 {
            for j in 1..i {
                let domain_i = EvaluationDomain::<Fr>::new(1 << i).unwrap();
                let domain_j = EvaluationDomain::<Fr>::new(1 << j).unwrap();
                let point = domain_j.sample_element_outside_domain(&mut rng);
                let j_elements = domain_j.elements().collect::<Vec<_>>();
                let slow_selector = {
                    let evals = domain_i
                        .elements()
                        .map(|e| if j_elements.contains(&e) { Fr::one() } else { Fr::zero() })
                        .collect();
                    Evaluations::from_vec_and_domain(evals, domain_i).interpolate()
                };
                assert_eq!(slow_selector.evaluate(point), domain_i.evaluate_selector_polynomial(domain_j, point));

                for element in domain_i.elements() {
                    if j_elements.contains(&element) {
                        assert_eq!(slow_selector.evaluate(element), Fr::one(), "failed for {i} vs {j}");
                    } else {
                        assert_eq!(slow_selector.evaluate(element), Fr::zero());
                    }
                }
            }
        }
    }
}
