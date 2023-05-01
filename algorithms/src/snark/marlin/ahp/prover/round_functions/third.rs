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

use core::convert::TryInto;
use std::collections::BTreeMap;

use crate::{
    fft::{
        domain::{FFTPrecomputation, IFFTPrecomputation},
        polynomial::PolyMultiplier,
        DensePolynomial,
        EvaluationDomain,
        Evaluations as EvaluationsOnDomain,
    },
    polycommit::sonic_pc::{LabeledPolynomial, PolynomialInfo, PolynomialLabel},
    snark::marlin::{
        ahp::{indexer::CircuitInfo, verifier, AHPError, AHPForR1CS, CircuitId},
        matrices::MatrixArithmetization,
        prover,
        witness_label,
        MarlinMode,
    },
};
use snarkvm_fields::{batch_inversion_and_mul, PrimeField};
use snarkvm_utilities::{cfg_iter, cfg_iter_mut, ExecutionPool};

use itertools::Itertools;
use rand_core::RngCore;

#[cfg(not(feature = "serial"))]
use rayon::prelude::*;

type Sum<F> = F;
type Lhs<F> = DensePolynomial<F>;
type Gpoly<F> = LabeledPolynomial<F>;

impl<F: PrimeField, MM: MarlinMode> AHPForR1CS<F, MM> {
    /// Output the number of oracles sent by the prover in the third round.
    pub fn num_third_round_oracles(circuits: usize) -> usize {
        circuits * 3
    }

    /// Output the degree bounds of oracles in the third round.
    pub fn third_round_polynomial_info<'a>(
        circuits: impl Iterator<Item = (CircuitId, &'a CircuitInfo<F>)>,
    ) -> BTreeMap<PolynomialLabel, PolynomialInfo> {
        circuits
            .flat_map(|(circuit_id, circuit_info)| {
                let non_zero_a_size =
                    EvaluationDomain::<F>::compute_size_of_domain(circuit_info.num_non_zero_a).unwrap();
                let non_zero_b_size =
                    EvaluationDomain::<F>::compute_size_of_domain(circuit_info.num_non_zero_b).unwrap();
                let non_zero_c_size =
                    EvaluationDomain::<F>::compute_size_of_domain(circuit_info.num_non_zero_c).unwrap();

                [
                    PolynomialInfo::new(witness_label(circuit_id, "g_a", 0), Some(non_zero_a_size - 2), None),
                    PolynomialInfo::new(witness_label(circuit_id, "g_b", 0), Some(non_zero_b_size - 2), None),
                    PolynomialInfo::new(witness_label(circuit_id, "g_c", 0), Some(non_zero_c_size - 2), None),
                ]
                .into_iter()
                .map(|info| (info.label().into(), info))
                .collect::<BTreeMap<PolynomialLabel, PolynomialInfo>>()
            })
            .collect()
    }

    /// Output the third round message and the next state.
    pub fn prover_third_round<'a, R: RngCore>(
        verifier_message: &verifier::SecondMessage<F>,
        mut state: prover::State<'a, F, MM>,
        _r: &mut R,
    ) -> Result<(prover::ThirdMessage<F>, prover::ThirdOracles<F>, prover::State<'a, F, MM>), AHPError> {
        let round_time = start_timer!(|| "AHP::Prover::ThirdRound");

        let verifier::FirstMessage { alpha, .. } = state
            .verifier_first_message
            .as_ref()
            .expect("prover::State should include verifier_first_msg when prover_third_round is called");

        let beta = verifier_message.beta;

        let mut pool = ExecutionPool::with_capacity(3 * state.circuit_specific_states.len());

        let largest_non_zero_domain_size = state.max_non_zero_domain.size_as_field_element;
        for (circuit, circuit_state) in &state.circuit_specific_states {
            let v_H_i_at_alpha = circuit_state.constraint_domain.evaluate_vanishing_polynomial(*alpha);
            let v_H_i_at_beta = circuit_state.constraint_domain.evaluate_vanishing_polynomial(beta);
            let v_H_i_alpha_v_H_i_beta = v_H_i_at_alpha * v_H_i_at_beta;

            let label_g_a = witness_label(circuit.id, "g_a", 0);
            pool.add_job(move || {
                let result = Self::matrix_sumcheck_helper(
                    label_g_a,
                    circuit_state.non_zero_a_domain,
                    &circuit.a_arith,
                    *alpha,
                    beta,
                    v_H_i_alpha_v_H_i_beta,
                    largest_non_zero_domain_size,
                    &circuit.fft_precomputation,
                    &circuit.ifft_precomputation,
                );
                (*circuit, result)
            });

            let label_g_b = witness_label(circuit.id, "g_b", 0);
            pool.add_job(move || {
                let result = Self::matrix_sumcheck_helper(
                    label_g_b,
                    circuit_state.non_zero_b_domain,
                    &circuit.b_arith,
                    *alpha,
                    beta,
                    v_H_i_alpha_v_H_i_beta,
                    largest_non_zero_domain_size,
                    &circuit.fft_precomputation,
                    &circuit.ifft_precomputation,
                );
                (*circuit, result)
            });

            let label_g_c = witness_label(circuit.id, "g_c", 0);
            pool.add_job(move || {
                let result = Self::matrix_sumcheck_helper(
                    label_g_c,
                    circuit_state.non_zero_c_domain,
                    &circuit.c_arith,
                    *alpha,
                    beta,
                    v_H_i_alpha_v_H_i_beta,
                    largest_non_zero_domain_size,
                    &circuit.fft_precomputation,
                    &circuit.ifft_precomputation,
                );
                (*circuit, result)
            });
        }

        let mut sums = Vec::with_capacity(state.circuit_specific_states.len());
        let mut gs = BTreeMap::new();
        for ((circuit_a, (sum_a, lhs_a, g_a)), (circuit_b, (sum_b, lhs_b, g_b)), (circuit_c, (sum_c, lhs_c, g_c))) in
            pool.execute_all().into_iter().tuples()
        {
            assert_eq!(circuit_a, circuit_b);
            assert_eq!(circuit_a, circuit_c);
            let matrix_sum = prover::message::MatrixSums { sum_a, sum_b, sum_c };
            sums.push(matrix_sum);
            state.circuit_specific_states.get_mut(circuit_a).unwrap().lhs_polynomials = Some([lhs_a, lhs_b, lhs_c]);
            let matrix_gs = prover::MatrixGs { g_a, g_b, g_c };
            gs.insert(circuit_a.id, matrix_gs);
        }

        let msg = prover::ThirdMessage { sums };
        let oracles = prover::ThirdOracles { gs };

        assert!(oracles.matches_info(&Self::third_round_polynomial_info(
            state.circuit_specific_states.keys().map(|c| (c.id, &c.index_info))
        )));

        end_timer!(round_time);

        Ok((msg, oracles, state))
    }

    #[allow(clippy::too_many_arguments)]
    fn matrix_sumcheck_helper(
        label: String,
        non_zero_domain: EvaluationDomain<F>,
        arithmetization: &MatrixArithmetization<F>,
        alpha: F,
        beta: F,
        v_H_i_alpha_v_H_i_beta: F,
        largest_non_zero_domain_size: F,
        fft_precomputation: &FFTPrecomputation<F>,
        ifft_precomputation: &IFFTPrecomputation<F>,
    ) -> (Sum<F>, Lhs<F>, Gpoly<F>) {
        let mut job_pool = snarkvm_utilities::ExecutionPool::with_capacity(2);
        job_pool.add_job(|| {
            let a_poly_time = start_timer!(|| format!("Computing a poly for {label}"));
            let a_poly = {
                let coeffs = cfg_iter!(arithmetization.val.as_dense().unwrap().coeffs())
                    .map(|a| v_H_i_alpha_v_H_i_beta * a)
                    .collect();
                DensePolynomial::from_coefficients_vec(coeffs)
            };
            end_timer!(a_poly_time);
            a_poly
        });

        let (row_on_K, col_on_K, row_col_on_K) =
            (&arithmetization.evals_on_K.row, &arithmetization.evals_on_K.col, &arithmetization.evals_on_K.row_col);

        job_pool.add_job(|| {
            let b_poly_time = start_timer!(|| format!("Computing b poly for {label}"));
            let alpha_beta = alpha * beta;
            let b_poly = {
                let evals: Vec<F> = cfg_iter!(row_on_K.evaluations)
                    .zip_eq(&col_on_K.evaluations)
                    .zip_eq(&row_col_on_K.evaluations)
                    .map(|((r, c), r_c)| alpha_beta - alpha * r - beta * c + r_c)
                    .collect();
                EvaluationsOnDomain::from_vec_and_domain(evals, non_zero_domain)
                    .interpolate_with_pc(ifft_precomputation)
            };
            end_timer!(b_poly_time);
            b_poly
        });
        let [a_poly, b_poly]: [_; 2] = job_pool.execute_all().try_into().unwrap();

        let f_evals_time = start_timer!(|| format!("Computing f evals on K for {label}"));
        let mut inverses: Vec<_> = cfg_iter!(row_on_K.evaluations)
            .zip_eq(&col_on_K.evaluations)
            .map(|(r, c)| (beta - r) * (alpha - c))
            .collect();
        batch_inversion_and_mul(&mut inverses, &v_H_i_alpha_v_H_i_beta);

        cfg_iter_mut!(inverses).zip_eq(&arithmetization.evals_on_K.val.evaluations).for_each(|(inv, a)| *inv *= a);
        let f_evals_on_K = inverses;
        end_timer!(f_evals_time);

        let f_poly_time = start_timer!(|| format!("Computing f poly for {label}"));
        // we define f as the rational equation for which we're running the sumcheck protocol
        let f = EvaluationsOnDomain::from_vec_and_domain(f_evals_on_K, non_zero_domain)
            .interpolate_with_pc(ifft_precomputation);
        end_timer!(f_poly_time);
        let g = DensePolynomial::from_coefficients_slice(&f.coeffs[1..]);
        let h = &a_poly
            - &{
                let mut multiplier = PolyMultiplier::new();
                multiplier.add_polynomial_ref(&b_poly, "b");
                multiplier.add_polynomial_ref(&f, "f");
                multiplier.add_precomputation(fft_precomputation, ifft_precomputation);
                multiplier.multiply().unwrap()
            };
        // Let K_max = largest_non_zero_domain;
        // Let K = non_zero_domain;
        // Let s := K_max.selector_polynomial(K) = (v_K_max / v_K) * (K.size() / K_max.size());
        // Let v_K_max := K_max.vanishing_polynomial();
        // Let v_K := K.vanishing_polynomial();
        // Let lhs := h / v_K * (K.size() / K_max.size());

        // Later on, we multiply `h` by s, and divide by v_K.
        // Substituting in s, we get that h * s / v_K_max = h / v_K * (K.size() / K_max.size());
        // That's what we're computing here.
        assert_eq!(h, &a_poly - &(&b_poly * &f));
        let (mut lhs, remainder) = h.divide_by_vanishing_poly(non_zero_domain).unwrap();
        assert!(remainder.is_zero());
        let multiplier = non_zero_domain.size_as_field_element / largest_non_zero_domain_size;
        cfg_iter_mut!(lhs.coeffs).for_each(|c| *c *= multiplier);

        let g = LabeledPolynomial::new(label, g, Some(non_zero_domain.size() - 2), None);

        assert!(lhs.degree() <= non_zero_domain.size() - 2);
        assert!(g.degree() <= non_zero_domain.size() - 2);
        (f.coeffs[0], lhs, g)
    }
}
