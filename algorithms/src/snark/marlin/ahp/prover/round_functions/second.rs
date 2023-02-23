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
    fft,
    fft::{
        domain::IFFTPrecomputation,
        polynomial::PolyMultiplier,
        DensePolynomial,
        EvaluationDomain,
        SparsePolynomial,
    },
    polycommit::sonic_pc::{LabeledPolynomial, PolynomialInfo, PolynomialLabel},
    snark::marlin::{
        ahp::{
            indexer::{Circuit, CircuitInfo, Matrix},
            verifier,
            AHPForR1CS,
            UnnormalizedBivariateLagrangePoly,
        },
        prover,
        MarlinMode,
    },
};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{cfg_iter, cfg_iter_mut, ExecutionPool};

use itertools::Itertools;
use rand_core::RngCore;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

enum BatchTerms {
    SZM,
    T,
}

impl<F: PrimeField, MM: MarlinMode> AHPForR1CS<F, MM> {

    /// Output the number of oracles sent by the prover in the second round.
    pub fn num_second_round_oracles() -> usize {
        2
    }

    /// Output the degree bounds of oracles in the first round.
    pub fn second_round_polynomial_info(info: &CircuitInfo<F>) -> BTreeMap<PolynomialLabel, PolynomialInfo> {
        let constraint_domain_size = EvaluationDomain::<F>::compute_size_of_domain(info.num_constraints).unwrap();
        [
            PolynomialInfo::new("g_1".into(), Some(constraint_domain_size - 2), Self::zk_bound()),
            PolynomialInfo::new("h_1".into(), None, None),
        ]
        .into_iter()
        .map(|info| (info.label().into(), info))
        .collect()
    }

    /// Output the second round message and the next state.
    // TODO: strategy will be very similar to matrix_sumcheck:
    // multiply per-circuit sumcheck equation by the selector polynomial * randomizer,
    // and then sum over all of these circuit-specific equations.
    pub fn prover_second_round<'a, R: RngCore>(
        verifier_message: &verifier::FirstMessage<'a, F, MM>,
        mut state: prover::State<'a, F, MM>,
        _r: &mut R,
    ) -> (prover::SecondOracles<F>, prover::State<'a, F, MM>) {
        let round_time = start_timer!(|| "AHP::Prover::SecondRound");

        let zk_bound = Self::zk_bound();

        let verifier::FirstMessage { alpha, eta_b, eta_c, batch_combiners } = verifier_message;

        let summed_z_m_and_t = Self::calculate_summed_z_m_and_t(&state, *alpha, *eta_b, *eta_c, batch_combiners);

        let max_constraint_domain = state.max_constraint_domain;

        let sumcheck_lhs = Self::calculate_lhs(&state, batch_combiners, summed_z_m_and_t, alpha);

        debug_assert!(
            sumcheck_lhs.evaluate_over_domain_by_ref(max_constraint_domain).evaluations.into_iter().sum::<F>().is_zero()
        );

        let sumcheck_time = start_timer!(|| "Compute sumcheck h and g polys");
        let (h_1, x_g_1) = sumcheck_lhs.divide_by_vanishing_poly(max_constraint_domain).unwrap();
        let g_1 = DensePolynomial::from_coefficients_slice(&x_g_1.coeffs[1..]);
        drop(x_g_1);
        end_timer!(sumcheck_time);

        assert!(g_1.degree() <= max_constraint_domain.size() - 2);
        assert!(h_1.degree() <= 2 * max_constraint_domain.size() + 2 * zk_bound.unwrap_or(0) - 2);

        let oracles = prover::SecondOracles {
            g_1: LabeledPolynomial::new("g_1".into(), g_1, Some(max_constraint_domain.size() - 2), zk_bound),
            h_1: LabeledPolynomial::new("h_1".into(), h_1, None, None),
        };
        assert!(oracles.matches_info(&Self::second_round_polynomial_info(&state.index.index_info)));

        state.verifier_first_message = Some(verifier_message.clone());
        end_timer!(round_time);

        (oracles, state)
    }

    fn calculate_lhs<'a>(
        state: &prover::State<F, MM>,
        batch_combiners: &BTreeMap<&Circuit<F, MM>, verifier::BatchCombiners<F>>,
        summed_z_m_and_t: BTreeMap<(&'a Circuit<F, MM>, BatchTerms), DensePolynomial<F>>,
        alpha: F,
    ) -> DensePolynomial<F> {

        let mut job_pool = ExecutionPool::with_capacity(2 * state.circuit_specific_states.len());

        cfg_iter!(state.first_round_oracles.as_ref().unwrap().batches).map(|batch| {
            let circuit_specific_state = state.circuit_specific_states[batch.0];
            let summed_z_m = summed_z_m_and_t[(batch.0, BatchTerms::SZM)];
            let t = summed_z_m_and_t[(batch.0, BatchTerms::T)];
            let circuit_combiner = batch_combiners[batch.0].circuit_combiner;

            job_pool.add_job(|| {
                let z_time = start_timer!(|| "Compute z poly"); // TODO: annotate with circuit index
                let z = cfg_iter!(batch.1)
                    .zip_eq(batch_combiners[batch.0])
                    .zip(&circuit_specific_state.x_polys)
                    .map(|((oracles, &instance_combiner), x_poly)| {
                        let mut z = oracles.w_poly.polynomial().as_dense().unwrap().mul_by_vanishing_poly(circuit_specific_state.input_domain);
                        // Zip safety: `x_poly` is smaller than `z_poly`.
                        z.coeffs.iter_mut().zip(&x_poly.coeffs).for_each(|(z, x)| *z += x);
                        cfg_iter_mut!(z.coeffs).for_each(|z| *z *= &instance_combiner);
                        z
                    })
                    .sum::<DensePolynomial<F>>();
                assert!(z.degree() <= circuit_specific_state.constraint_domain.size());

                end_timer!(z_time);

                let mut circuit_specific_lhs = Self::calculate_circuit_specific_lhs(&circuit_specific_state, t, summed_z_m, z, *alpha);
                circuit_specific_lhs *= circuit_combiner;
                circuit_specific_lhs
            });
        });

        // TODO: sum over index_specific_lhs, multiplying by the selector polynomial * randomizer.
        // Selector polynomial = v_H_max / v_H.
        // Use the same trick from the matrix sumcheck to avoid unnecessary multiplications.
        //
        // Comments from that section duplicated here for convenience:
        // Let K_max = largest_non_zero_domain;
        // Let K = non_zero_domain;
        // Let s := K_max.selector_polynomial(K) = (v_K_max / v_K) * (K.size() / K_max.size());
        // Let v_K_max := K_max.vanishing_polynomial();
        // Let v_K := K.vanishing_polynomial();

        // Later on, we multiply `h` by s, and divide by v_K_max.
        // Substituting in s, we get that h * s / v_K_max = h / v_K * (K.size() / K_max.size());
        // That's what we're computing here.

        // TODO: check if annotation is required
        let circuit_specific_lhs_s: Vec<DensePolynomial<F>> = job_pool.execute_all().try_into().unwrap();
        let mut lhs_sum = circuit_specific_lhs_s.sum();

        let mask_poly = state.first_round_oracles.as_ref().unwrap().mask_poly.as_ref();
        assert_eq!(MM::ZK, mask_poly.is_some());
        lhs_sum += &mask_poly.map_or(SparsePolynomial::zero(), |p| p.polynomial().as_sparse().unwrap().clone());
        lhs_sum
    }

    fn calculate_circuit_specific_lhs(
        state: &prover::CircuitSpecificState<F>,
        t: DensePolynomial<F>,
        summed_z_m: DensePolynomial<F>,
        z: DensePolynomial<F>,
        alpha: F,
    ) -> DensePolynomial<F> {
        let constraint_domain = state.constraint_domain;
        let q_1_time = start_timer!(|| "Compute LHS of sumcheck");

        let mul_domain_size = (constraint_domain.size() + summed_z_m.coeffs.len()).max(t.coeffs.len() + z.len());
        let mul_domain =
            EvaluationDomain::new(mul_domain_size).expect("field is not smooth enough to construct domain");
        let mut multiplier = PolyMultiplier::new();
        multiplier.add_precomputation(state.fft_precomputation(), state.ifft_precomputation());
        multiplier.add_polynomial(summed_z_m, "summed_z_m");
        multiplier.add_polynomial(z, "z");
        multiplier.add_polynomial(t, "t");
        let r_alpha_x_evals = {
            let r_alpha_x_evals = constraint_domain
                .batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs_over_domain(alpha, &mul_domain);
            fft::Evaluations::from_vec_and_domain(r_alpha_x_evals, mul_domain)
        };
        multiplier.add_evaluation(r_alpha_x_evals, "r_alpha_x");
        let mut lhs = multiplier
            .element_wise_arithmetic_4_over_domain(mul_domain, ["r_alpha_x", "summed_z_m", "z", "t"], |a, b, c, d| {
                a * b - c * d
            })
            .unwrap();

        end_timer!(q_1_time);
        lhs
    }

    fn calculate_summed_z_m_and_t<'a>(
        state: &prover::State<F, MM>,
        alpha: F,
        eta_b: F,
        eta_c: F,
        batch_combiners: &BTreeMap<&'a Circuit<F, MM>, verifier::BatchCombiners<F>>,
    ) -> BTreeMap<(&'a Circuit<F, MM>, BatchTerms), DensePolynomial<F>> {
        let constraint_domain = state.max_constraint_domain;
        let first_msg = state.first_round_oracles.as_ref().unwrap();

        assert!(batch_combiners.len() == state.circuit_specific_states.len());
        let mut job_pool = ExecutionPool::with_capacity(2 * state.circuit_specific_states.len());

        cfg_iter!(state.circuit_specific_states)
            .map(|circuit_state| {
                let fft_precomputation = &circuit_state.0.fft_precomputation;
                let ifft_precomputation = &circuit_state.0.ifft_precomputation;
                let eta_b_over_eta_c = eta_b * eta_c.inverse().unwrap();
                job_pool.add_job(|| {
                    let summed_z_m_poly_time = start_timer!(|| "Compute z_m poly"); // TODO: timers should get a label
                    let summed_z_m = cfg_iter!(first_msg.batches[circuit_state.0])
                        .zip_eq(batch_combiners[circuit_state.0].instance_combiners)
                        .map(|(entry, combiner)| {
                            let z_a = entry.z_a_poly.polynomial().as_dense().unwrap();
                            let mut z_b = entry.z_b_poly.polynomial().as_dense().unwrap().clone();
                            assert!(z_a.degree() < constraint_domain.size());
                            if MM::ZK {
                                assert_eq!(z_b.degree(), constraint_domain.size());
                            } else {
                                assert!(z_b.degree() < constraint_domain.size());
                            }
        
                            // we want to calculate r_i * (z_a + eta_b * z_b + eta_c * z_a * z_b);
                            // we rewrite this as  r_i * (z_a * (eta_c * z_b + 1) + eta_b * z_b);
                            // This is better since it reduces the number of required
                            // multiplications by `constraint_domain.size()`.
                            let mut summed_z_m = {
                                // Mutate z_b in place to compute eta_c * z_b + 1
                                // This saves us an additional memory allocation.
                                cfg_iter_mut!(z_b.coeffs).for_each(|b| *b *= eta_c);
                                z_b.coeffs[0] += F::one();
                                let mut multiplier = PolyMultiplier::new();
                                multiplier.add_polynomial_ref(z_a, "z_a");
                                multiplier.add_polynomial_ref(&z_b, "eta_c_z_b_plus_one");
                                multiplier.add_precomputation(fft_precomputation, ifft_precomputation);
                                let result = multiplier.multiply().unwrap();
                                // Start undoing in place mutation, by first subtracting the 1 that we added...
                                z_b.coeffs[0] -= F::one();
                                result
                            };
                            // ... and then multiplying by eta_b/eta_c, instead of just eta_b.
                            cfg_iter_mut!(summed_z_m.coeffs).zip(&z_b.coeffs).for_each(|(c, b)| *c += eta_b_over_eta_c * b);
        
                            // Multiply by linear combination coefficient.
                            cfg_iter_mut!(summed_z_m.coeffs).for_each(|c| *c *= *combiner);

                            assert_eq!(summed_z_m.degree(), z_a.degree() + z_b.degree());
                            end_timer!(summed_z_m_poly_time);
                            summed_z_m
                        })
                        .sum::<DensePolynomial<_>>();
                    ((circuit_state.0, BatchTerms::SZM), summed_z_m)
                });
        
                job_pool.add_job(|| {
                    let t_poly_time = start_timer!(|| "Compute t poly"); // TODO: this should get a label
        
                    let r_alpha_x_evals =
                        constraint_domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(alpha);
                    let t = Self::calculate_t(
                        &[&circuit_state.1.a, &circuit_state.1.b, &circuit_state.1.c],
                        [F::one(), eta_b, eta_c],
                        &state.input_domain,
                        &state.constraint_domain,
                        &r_alpha_x_evals,
                        ifft_precomputation,
                    );
                    end_timer!(t_poly_time);
                    ((circuit_state.0, BatchTerms::T), t)
                });
            });

        // BTreeMap with 2*batch_combiners.len() entries
        // TODO: annotation might be unnecessary because the return type of the function is already indicated
        let summed_z_m_and_t: BTreeMap<(&'a Circuit<F, MM>, BatchTerms), DensePolynomial<F>> = job_pool.execute_all().try_into().unwrap();
        summed_z_m_and_t
    }

    fn calculate_t<'a>(
        matrices: &[&'a Matrix<F>],
        matrix_randomizers: [F; 3],
        input_domain: &EvaluationDomain<F>,
        constraint_domain: &EvaluationDomain<F>,
        r_alpha_x_on_h: &[F],
        ifft_precomputation: &IFFTPrecomputation<F>,
    ) -> DensePolynomial<F> {
        let mut t_evals_on_h = vec![F::zero(); constraint_domain.size()];
        for (matrix, eta) in matrices.iter().zip_eq(matrix_randomizers) {
            for (r, row) in matrix.iter().enumerate() {
                for (coeff, c) in row.iter() {
                    let index = constraint_domain.reindex_by_subdomain(input_domain, *c);
                    t_evals_on_h[index] += &(eta * coeff * r_alpha_x_on_h[r]);
                }
            }
        }
        fft::Evaluations::from_vec_and_domain(t_evals_on_h, *constraint_domain).interpolate_with_pc(ifft_precomputation)
    }
}
