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
        ahp::{indexer::Circuit, verifier, AHPError, AHPForR1CS},
        matrices::MatrixArithmetization,
        prover,
        MarlinMode,
        witness_label,
    },
};
use snarkvm_fields::{batch_inversion_and_mul, PrimeField};
use snarkvm_utilities::{cfg_iter, cfg_iter_mut, ExecutionPool};

use rand_core::RngCore;

#[cfg(not(feature = "parallel"))]
use itertools::Itertools;
#[cfg(feature = "parallel")]
use rayon::prelude::*;

type Sum<F> = F;
type LHS<F> = DensePolynomial<F>;
type Gpoly<F> = LabeledPolynomial<F>;
struct SumcheckHelperResult<F>(Sum<F>, LHS<F>, Gpoly<F>);

impl<F: PrimeField, MM: MarlinMode> AHPForR1CS<F, MM> {
    /// Output the number of oracles sent by the prover in the third round.
    // TODO: update this according to the number of circuits (3 * num_circuits).
    pub fn num_third_round_oracles() -> usize {
        3
    }

    /// Output the degree bounds of oracles in the first round.
    // TODO: to verify if this is correct, see if we're 'consuming' this information in a similar way to the first round
    pub fn third_round_polynomial_info<'a>(
        circuits: impl Iterator<Item = (&'a Circuit<F, MM>, usize)>
    ) -> BTreeMap<PolynomialLabel, PolynomialInfo> {
        let mut polynomials = circuits.flat_map(|(circuit, batch_size)| {
            let circuit_id = format!("circuit_{:x?}", circuit.hash);

            let non_zero_a_size = EvaluationDomain::<F>::compute_size_of_domain(circuit.index_info.num_non_zero_a).unwrap();
            let non_zero_b_size = EvaluationDomain::<F>::compute_size_of_domain(circuit.index_info.num_non_zero_b).unwrap();
            let non_zero_c_size = EvaluationDomain::<F>::compute_size_of_domain(circuit.index_info.num_non_zero_c).unwrap();
    
            (0..batch_size).flat_map(|i| {
                [   
                    PolynomialInfo::new(witness_label(&circuit_id, "g_a", i), Some(non_zero_a_size - 2), None),
                    PolynomialInfo::new(witness_label(&circuit_id, "g_b", i), Some(non_zero_b_size - 2), None),
                    PolynomialInfo::new(witness_label(&circuit_id, "g_c", i), Some(non_zero_c_size - 2), None)
                ]
            })
        }).collect::<Vec<_>>();
    }

    /// Output the third round message and the next state.
    pub fn prover_third_round<'a, R: RngCore>(
        verifier_message: &verifier::SecondMessage<F>,
        mut state: prover::State<'a, F, MM>,
        _r: &mut R,
    ) -> Result<(prover::ThirdMessage<'a, F, MM>, prover::ThirdOracles<'a, F, MM>, prover::State<'a, F, MM>), AHPError> {
        let round_time = start_timer!(|| "AHP::Prover::ThirdRound");

        let verifier::FirstMessage { alpha, .. } = state
            .verifier_first_message
            .as_ref()
            .expect("prover::State should include verifier_first_msg when prover_third_round is called");

        let beta = verifier_message.beta;

        let v_H_at_alpha = state.constraint_domain.evaluate_vanishing_polynomial(*alpha);
        let v_H_at_beta = state.constraint_domain.evaluate_vanishing_polynomial(beta);

        let v_H_alpha_v_H_beta = v_H_at_alpha * v_H_at_beta;

        let mut pool = ExecutionPool::with_capacity(3*state.circuit_specific_states.len());

        for (circuit, circuit_state) in state.circuit_specific_states.iter() {
            let largest_non_zero_domain_size = Self::max_non_zero_domain(&circuit_state.0.index_info).size_as_field_element;
            pool.add_job(|| {
                let result = Self::matrix_sumcheck_helper(
                    "a",
                    circuit_state.non_zero_a_domain,
                    &circuit_state.index.a_arith,
                    *alpha,
                    beta,
                    v_H_alpha_v_H_beta,
                    largest_non_zero_domain_size,
                    circuit_state.fft_precomputation(),
                    circuit_state.ifft_precomputation(),
                );
                (circuit, result)
            });

            pool.add_job(|| {
                let result = Self::matrix_sumcheck_helper(
                    "b",
                    circuit_state.non_zero_b_domain,
                    &circuit_state.index.b_arith,
                    *alpha,
                    beta,
                    v_H_alpha_v_H_beta,
                    largest_non_zero_domain_size,
                    circuit_state.fft_precomputation(),
                    circuit_state.ifft_precomputation(),
                );
                (circuit, result)
            });

            pool.add_job(|| {
                let result = Self::matrix_sumcheck_helper(
                    "c",
                    circuit_state.non_zero_c_domain,
                    &circuit_state.index.c_arith,
                    *alpha,
                    beta,
                    v_H_alpha_v_H_beta,
                    largest_non_zero_domain_size,
                    circuit_state.fft_precomputation(),
                    circuit_state.ifft_precomputation(),
                );
                (circuit, result)
            });
        }

        // TODO: check we're not making unnecessary copies
        let sums: BTreeMap<&'a Circuit<F, MM>, prover::message::MatrixSums> = BTreeMap::new();
        let gs: BTreeMap<&'a Circuit<F, MM>, prover::MatrixGs> = BTreeMap::new();
        for res in pool.execute_all().tuples() {
            let (a, b, c): ((&'a Circuit<F, MM>, SumcheckHelperResult<F>), (&'a Circuit<F, MM>, SumcheckHelperResult<F>), (&'a Circuit<F, MM>, SumcheckHelperResult<F>)) = res;
            assert!(a.0 == b.0 && b.0 == c.0);
            state.circuit_specific_states[a.0].sums = Some([a.1[0], b.1[0], c.1[0]]); // TODO: where do we use this? We're saving the state twice, which is a waste
            let matrix_sum = prover::message::MatrixSums {
                sum_a: a.1.0,
                sum_b: b.1.0,
                sum_c: c.1.0,
            };
            sums.insert(a.0, matrix_sum);
            state.circuit_specific_states[a.0].lhs_polynomials = Some([a.1.1, b.1.1, c.1.1]);
            let matrix_gs = prover::MatrixGs {
                g_a: a.1.2,
                g_b: b.1.2,
                g_c: c.1.2,
            };
            gs.insert(a.0, matrix_gs);
        }

        let msg = prover::ThirdMessage { sums };
        let oracles = prover::ThirdOracles { gs };

        assert!(oracles.matches_info(&Self::third_round_polynomial_info(state.circuit_specific_states.iter().map(|(c, s)| (*c, s.batch_size)))));

        end_timer!(round_time);

        Ok((msg, oracles, state))
    }

    #[allow(clippy::too_many_arguments)]
    fn matrix_sumcheck_helper(
        label: &str,
        non_zero_domain: EvaluationDomain<F>,
        arithmetization: &MatrixArithmetization<F>,
        alpha: F,
        beta: F,
        v_H_alpha_v_H_beta: F,
        largest_non_zero_domain_size: F,
        fft_precomputation: &FFTPrecomputation<F>,
        ifft_precomputation: &IFFTPrecomputation<F>,
    ) -> (Sum<F>, LHS<F>, Gpoly<F>){
        let mut job_pool = snarkvm_utilities::ExecutionPool::with_capacity(2);
        job_pool.add_job(|| {
            let a_poly_time = start_timer!(|| "Computing a poly");
            let a_poly = {
                let coeffs = cfg_iter!(arithmetization.val.as_dense().unwrap().coeffs())
                    .map(|a| v_H_alpha_v_H_beta * a)
                    .collect();
                DensePolynomial::from_coefficients_vec(coeffs)
            };
            end_timer!(a_poly_time);
            a_poly
        });

        let (row_on_K, col_on_K, row_col_on_K) =
            (&arithmetization.evals_on_K.row, &arithmetization.evals_on_K.col, &arithmetization.evals_on_K.row_col);

        job_pool.add_job(|| {
            let b_poly_time = start_timer!(|| "Computing b poly");
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

        let f_evals_time = start_timer!(|| "Computing f evals on K");
        let mut inverses: Vec<_> = cfg_iter!(row_on_K.evaluations)
            .zip_eq(&col_on_K.evaluations)
            .map(|(r, c)| (beta - r) * (alpha - c))
            .collect();
        batch_inversion_and_mul(&mut inverses, &v_H_alpha_v_H_beta);

        cfg_iter_mut!(inverses).zip_eq(&arithmetization.evals_on_K.val.evaluations).for_each(|(inv, a)| *inv *= a);
        let f_evals_on_K = inverses;
        end_timer!(f_evals_time);

        let f_poly_time = start_timer!(|| "Computing f poly");
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

        // Later on, we multiply `h` by s, and divide by v_K_max.
        // Substituting in s, we get that h * s / v_K_max = h / v_K * (K.size() / K_max.size());
        // That's what we're computing here.
        let (mut h, remainder) = h.divide_by_vanishing_poly(non_zero_domain).unwrap();
        assert!(remainder.is_zero());
        let multiplier = non_zero_domain.size_as_field_element / largest_non_zero_domain_size;
        cfg_iter_mut!(h.coeffs).for_each(|c| *c *= multiplier);

        let g = LabeledPolynomial::new("g_".to_string() + label, g, Some(non_zero_domain.size() - 2), None);

        assert!(h.degree() <= non_zero_domain.size() - 2);
        assert!(g.degree() <= non_zero_domain.size() - 2);
        (f.coeffs[0], h, g)
    }
}
