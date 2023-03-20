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
    fft,
    fft::{
        domain::{FFTPrecomputation, IFFTPrecomputation},
        polynomial::PolyMultiplier,
        DensePolynomial,
        EvaluationDomain,
        SparsePolynomial,
    },
    polycommit::sonic_pc::{LabeledPolynomial, PolynomialInfo, PolynomialLabel},
    snark::marlin::{
        ahp::{
            indexer::{CircuitId, Matrix},
            verifier,
            AHPForR1CS,
            UnnormalizedBivariateLagrangePoly,
        },
        prover,
        MarlinMode,
    },
    SNARKError,
};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{cfg_iter, cfg_iter_mut, ExecutionPool};

use itertools::Itertools;
use rand_core::RngCore;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

impl<F: PrimeField, MM: MarlinMode> AHPForR1CS<F, MM> {

    /// Output the degree bounds of oracles in the first round.
    pub fn second_round_polynomial_info(max_num_constraints: usize) -> BTreeMap<PolynomialLabel, PolynomialInfo> {
        let constraint_domain_size = EvaluationDomain::<F>::compute_size_of_domain(max_num_constraints).unwrap();
        [
            PolynomialInfo::new("g_1".into(), Some(constraint_domain_size - 2), Self::zk_bound()),
            PolynomialInfo::new("h_1".into(), None, None),
        ]
        .into_iter()
        .map(|info| (info.label().into(), info))
        .collect()
    }

    /// Output the second round message and the next state.
    pub fn prover_second_round<'a, R: RngCore>(
        verifier_message: &verifier::FirstMessage<'a, F>,
        mut state: prover::State<'a, F, MM>,
        _r: &mut R,
    ) -> (prover::SecondOracles<F>, prover::State<'a, F, MM>) {
        let round_time = start_timer!(|| "AHP::Prover::SecondRound");

        let zk_bound = Self::zk_bound();

        let verifier::FirstMessage { alpha, eta_b, eta_c, batch_combiners } = verifier_message;

        let summed_z_m_and_t = Self::calculate_summed_z_m_and_t(&state, *alpha, *eta_b, *eta_c, batch_combiners);

        let sumcheck_lhs = Self::calculate_lhs(&state, batch_combiners, summed_z_m_and_t, alpha);

        let max_constraint_domain = state.max_constraint_domain;

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
        assert!(oracles.matches_info(&Self::second_round_polynomial_info(state.max_num_constraints)));

        state.verifier_first_message = Some(verifier_message.clone());
        end_timer!(round_time);

        (oracles, state)
    }

    fn calculate_lhs<'a>(
        state: &prover::State<'a, F, MM>,
        batch_combiners: &BTreeMap<&'a CircuitId, verifier::BatchCombiners<F>>,
        mut summed_z_m_and_t: Vec<(&'a CircuitId, DensePolynomial<F>)>,
        alpha: &F,
    ) -> DensePolynomial<F> {

        let mut job_pool = ExecutionPool::with_capacity(state.circuit_specific_states.len());
        let max_constraint_domain_size = state.max_constraint_domain.size_as_field_element;

        for (i, (circuit, oracles)) in state.first_round_oracles.as_ref().unwrap().batches.iter().enumerate() {
            let circuit_specific_state = &state.circuit_specific_states[circuit];
            let summed_z_m = &mut summed_z_m_and_t[2*i];
            assert!(*summed_z_m.0 == circuit.hash);
            let summed_z_m = core::mem::take(&mut summed_z_m.1);
            let summed_t = &mut summed_z_m_and_t[2*i + 1];
            assert!(*summed_t.0 == circuit.hash);
            let summed_t = core::mem::take(&mut summed_t.1);
            let circuit_combiner = batch_combiners[&circuit.hash].circuit_combiner;
            let instance_combiners = batch_combiners[&circuit.hash].instance_combiners.clone();
            let x_polys = circuit_specific_state.x_polys.clone();
            let input_domain = circuit_specific_state.input_domain.clone();
            let constraint_domain = &circuit_specific_state.constraint_domain;
            let fft_precomputation = &circuit.fft_precomputation;
            let ifft_precomputation = &circuit.ifft_precomputation;
            let circuit_id = &circuit.hash;

            job_pool.add_job(move || {
                let z_time = start_timer!(|| format!("Compute z poly for circuit {:?}", circuit_id));
                let z = cfg_iter!(oracles)
                    .zip_eq(instance_combiners)
                    .zip(x_polys)
                    .map(|((oracles, instance_combiner), x_poly)| {
                        let mut z = oracles.w_poly.polynomial().as_dense().unwrap().mul_by_vanishing_poly(input_domain);
                        // Zip safety: `x_poly` is smaller than `z_poly`.
                        z.coeffs.iter_mut().zip(&x_poly.coeffs).for_each(|(z, x)| *z += x);
                        cfg_iter_mut!(z.coeffs).for_each(|z| *z *= instance_combiner);
                        z
                    })
                    .sum::<DensePolynomial<F>>();
                assert!(z.degree() <= constraint_domain.size());

                end_timer!(z_time);

                let mut circuit_specific_lhs = Self::calculate_circuit_specific_lhs(constraint_domain, fft_precomputation, ifft_precomputation, summed_t, summed_z_m, z, *alpha);
        
                // Naive setup:
                circuit_specific_lhs = circuit_specific_lhs.mul_by_vanishing_poly(state.max_constraint_domain);
                let (quotient, remainder) = circuit_specific_lhs.divide_by_vanishing_poly(*constraint_domain).unwrap();
                assert!(remainder.is_zero());
                circuit_specific_lhs = quotient * (constraint_domain.size_as_field_element / max_constraint_domain_size);
                circuit_specific_lhs *= circuit_combiner;

                // Let H = largest_domain;
                // Let H_i = domain;
                // Let v_H := H.vanishing_polynomial();
                // Let v_H_i := H_i.vanishing_polynomial();
                // Let s := H.selector_polynomial(H_i) = (v_H / v_H_i) * (H_i.size() / H.size());
                // Let m := masking polynomial

                // Later on, we multiply `lhs` by s, add m and divide by v_H.
                // Substituting in s, we get that (lhs * s + m) / v_H = (lhs / v_H_i) * (H_i.size() / H.size()) + m / v_H;
                // That's what we're computing here.

                // TODO: Potential optimization:
                // let (mut circuit_specific_lhs, remainder) = circuit_specific_lhs.divide_by_vanishing_poly(*constraint_domain).unwrap();
                // let multiplier = constraint_domain.size_as_field_element / max_constraint_domain_size;
                // cfg_iter_mut!(circuit_specific_lhs.coeffs).for_each(|c| *c *= multiplier);        
                // cfg_iter_mut!(remainder.coeffs).for_each(|c| *c *= multiplier);        
                // TODO: Can we just sum up all of the remainders, potentially carrying back to the quotient?
                // TODO: Would also still need to divide m by v_H 
                // TODO: remove division by v_H one level up the callchain.

                circuit_specific_lhs
            });
        }
        let circuit_specific_lhs_s: Vec<_> = job_pool.execute_all().try_into().unwrap();
        let mut lhs_sum = circuit_specific_lhs_s.into_iter().sum::<DensePolynomial<F>>();

        let mask_poly = state.first_round_oracles.as_ref().unwrap().mask_poly.as_ref();
        assert_eq!(MM::ZK, mask_poly.is_some());
        lhs_sum += &mask_poly.map_or(SparsePolynomial::zero(), |p| p.polynomial().as_sparse().unwrap().clone());
        lhs_sum
    }

    fn calculate_circuit_specific_lhs(
        constraint_domain: &EvaluationDomain<F>,
        fft_precomputation: &FFTPrecomputation<F>,
        ifft_precomputation: &IFFTPrecomputation<F>,
        t: DensePolynomial<F>,
        summed_z_m: DensePolynomial<F>,
        z: DensePolynomial<F>,
        alpha: F,
    ) -> DensePolynomial<F> {
        let q_1_time = start_timer!(|| "Compute LHS of sumcheck");

        let mul_domain_size = (constraint_domain.size() + summed_z_m.coeffs.len()).max(t.coeffs.len() + z.len());
        let mul_domain =
            EvaluationDomain::new(mul_domain_size).expect("field is not smooth enough to construct domain");
        let mut multiplier = PolyMultiplier::new();
        multiplier.add_precomputation(fft_precomputation, ifft_precomputation);
        multiplier.add_polynomial(summed_z_m, "summed_z_m");
        multiplier.add_polynomial(z, "z");
        multiplier.add_polynomial(t, "t");
        let r_alpha_x_evals = {
            let r_alpha_x_evals = constraint_domain
                .batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs_over_domain(alpha, &mul_domain);
            fft::Evaluations::from_vec_and_domain(r_alpha_x_evals, mul_domain)
        };
        multiplier.add_evaluation(r_alpha_x_evals, "r_alpha_x");
        let lhs = multiplier
            .element_wise_arithmetic_4_over_domain(mul_domain, ["r_alpha_x", "summed_z_m", "z", "t"], |a, b, c, d| {
                a * b - c * d
            })
            .unwrap();

        end_timer!(q_1_time);
        lhs
    }

    fn calculate_summed_z_m_and_t<'a>(
        state: &prover::State<'a, F, MM>,
        alpha: F,
        eta_b: F,
        eta_c: F,
        batch_combiners: &BTreeMap<&'a CircuitId, verifier::BatchCombiners<F>>,
    ) -> Vec<(&'a CircuitId, DensePolynomial<F>)> {
        let constraint_domain = state.max_constraint_domain;
        let first_msg = state.first_round_oracles.as_ref().unwrap();

        assert!(batch_combiners.len() == state.circuit_specific_states.len());
        let mut job_pool = ExecutionPool::with_capacity(2 * state.circuit_specific_states.len());

        for (circuit, circuit_specific_state) in state.circuit_specific_states.iter() {
            let fft_precomputation = &circuit.fft_precomputation;
            let ifft_precomputation = &circuit.ifft_precomputation;
            let eta_b_over_eta_c = eta_b * eta_c.inverse().unwrap();
            let first_msg_i = &first_msg.batches[circuit];
            let instance_combiners = &batch_combiners[&circuit.hash].instance_combiners;
            let circuit_id_z_m = &circuit.hash;
            let circuit_id_t = &circuit.hash;
            let circuit_constraint_domain = circuit_specific_state.constraint_domain;
            let circuit_input_domain = circuit_specific_state.input_domain;
            job_pool.add_job(move || {
                let summed_z_m_poly_time = start_timer!(|| format!("Compute z_m poly for circuit {:?}", circuit_id_z_m));
                let summed_z_m = cfg_iter!(first_msg_i)
                    .zip_eq(instance_combiners)
                    .map(|(entry, combiner)| {
                        let z_a = entry.z_a_poly.polynomial().as_dense().unwrap();
                        let mut z_b = entry.z_b_poly.polynomial().as_dense().unwrap().clone();
                        assert!(z_a.degree() < constraint_domain.size());
                        if MM::ZK {
                            assert_eq!(z_b.degree(), circuit_constraint_domain.size());
                        } else {
                            assert!(z_b.degree() < circuit_constraint_domain.size());
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
                        cfg_iter_mut!(summed_z_m.coeffs).for_each(|c| *c *= combiner);

                        assert_eq!(summed_z_m.degree(), z_a.degree() + z_b.degree());
                        end_timer!(summed_z_m_poly_time);
                        summed_z_m
                    })
                    .sum::<DensePolynomial<_>>();
                (circuit_id_z_m, summed_z_m)
            });
    
            job_pool.add_job(move || {
                let t_poly_time = start_timer!(|| format!("Compute t poly for circuit {:?}", circuit_id_t));

                let r_alpha_x_evals =
                    constraint_domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(alpha);
                let t = Self::calculate_t(
                    &[&circuit.a, &circuit.b, &circuit.c],
                    [F::one(), eta_b, eta_c],
                    &circuit_input_domain,
                    &circuit_constraint_domain,
                    &r_alpha_x_evals,
                    ifft_precomputation,
                );
                end_timer!(t_poly_time);
                (circuit_id_t, t)
            });
        }

        job_pool.execute_all().try_into().unwrap()
    }

    fn calculate_t(
        matrices: &[&Matrix<F>],
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
