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

use std::collections::BTreeMap;

use crate::{
    fft,
    fft::{
        domain::{FFTPrecomputation, IFFTPrecomputation},
        polynomial::PolyMultiplier,
        DensePolynomial,
        EvaluationDomain,
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
};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{cfg_iter, cfg_iter_mut, ExecutionPool};

use itertools::Itertools;
use rand_core::RngCore;

#[cfg(not(feature = "serial"))]
use rayon::prelude::*;

struct LincheckPoly<F: PrimeField> {
    circuit_id: CircuitId,
    poly: DensePolynomial<F>,
}

impl<F: PrimeField, MM: MarlinMode> AHPForR1CS<F, MM> {
    /// Output the number of oracles sent by the prover in the second round.
    pub fn num_second_round_oracles() -> usize {
        2
    }

    /// Output the degree bounds of oracles in the first round.
    pub fn second_round_polynomial_info(constraint_domain_size: usize) -> BTreeMap<PolynomialLabel, PolynomialInfo> {
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
        verifier_message: &verifier::FirstMessage<F>,
        mut state: prover::State<'a, F, MM>,
        _r: &mut R,
    ) -> (prover::SecondOracles<F>, prover::State<'a, F, MM>) {
        let round_time = start_timer!(|| "AHP::Prover::SecondRound");

        let zk_bound = Self::zk_bound();

        let max_constraint_domain = state.max_constraint_domain;

        let verifier::FirstMessage { alpha, eta_b, eta_c, batch_combiners } = verifier_message;

        let summed_z_m_and_t = Self::calculate_summed_z_m_and_t(&state, *alpha, *eta_b, *eta_c, batch_combiners);

        let (h_1, x_g_1) = Self::calculate_lhs(&mut state, batch_combiners, summed_z_m_and_t, alpha);

        let mut sumcheck_lhs = h_1.mul_by_vanishing_poly(max_constraint_domain);
        sumcheck_lhs += &x_g_1;
        debug_assert!(
            sumcheck_lhs
                .evaluate_over_domain_by_ref(max_constraint_domain)
                .evaluations
                .into_iter()
                .sum::<F>()
                .is_zero()
        );

        let g_1 = DensePolynomial::from_coefficients_slice(&x_g_1.coeffs[1..]);
        drop(x_g_1);

        assert!(g_1.degree() <= max_constraint_domain.size() - 2);
        assert!(h_1.degree() <= 2 * max_constraint_domain.size() + 2 * zk_bound.unwrap_or(0) - 2);

        let oracles = prover::SecondOracles {
            g_1: LabeledPolynomial::new("g_1".into(), g_1, Some(max_constraint_domain.size() - 2), zk_bound),
            h_1: LabeledPolynomial::new("h_1".into(), h_1, None, None),
        };
        assert!(oracles.matches_info(&Self::second_round_polynomial_info(state.max_constraint_domain.size())));

        state.verifier_first_message = Some(verifier_message.clone());
        end_timer!(round_time);

        (oracles, state)
    }

    fn calculate_lhs(
        state: &mut prover::State<F, MM>,
        batch_combiners: &BTreeMap<CircuitId, verifier::BatchCombiners<F>>,
        mut summed_z_m_and_t: Vec<LincheckPoly<F>>,
        alpha: &F,
    ) -> (DensePolynomial<F>, DensePolynomial<F>) {
        let mut job_pool = ExecutionPool::with_capacity(state.circuit_specific_states.len());
        let max_constraint_domain_inv = state.max_constraint_domain.size_inv;
        let max_constraint_domain = state.max_constraint_domain;

        for (i, ((circuit, circuit_specific_state), oracles)) in state
            .circuit_specific_states
            .iter_mut()
            .zip(state.first_round_oracles.as_ref().unwrap().batches.values())
            .enumerate()
        {
            let summed_z_m = &mut summed_z_m_and_t[2 * i];
            assert_eq!(summed_z_m.circuit_id, circuit.id); // does z_m belong to the right circuit?
            let summed_z_m = core::mem::take(&mut summed_z_m.poly);

            let summed_t = &mut summed_z_m_and_t[2 * i + 1];
            assert_eq!(summed_t.circuit_id, circuit.id); // does t belong to the right circuit?
            let summed_t = core::mem::take(&mut summed_t.poly);

            let circuit_combiner = batch_combiners[&circuit.id].circuit_combiner;
            let instance_combiners = batch_combiners[&circuit.id].instance_combiners.clone();
            let x_polys = core::mem::take(&mut circuit_specific_state.x_polys);
            let input_domain = circuit_specific_state.input_domain;
            let constraint_domain = circuit_specific_state.constraint_domain;
            let fft_precomputation = &circuit.fft_precomputation;
            let ifft_precomputation = &circuit.ifft_precomputation;

            let _circuit_id = &circuit.id; // seems like a compiler bug marks this as unused

            job_pool.add_job(move || {
                let z_time = start_timer!(move || format!("Compute z poly for circuit {_circuit_id}"));
                let z = cfg_iter!(oracles)
                    .zip_eq(instance_combiners)
                    .zip_eq(x_polys)
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

                let mut circuit_specific_lhs = Self::calculate_circuit_specific_lhs(
                    &constraint_domain,
                    fft_precomputation,
                    ifft_precomputation,
                    summed_t,
                    summed_z_m,
                    z,
                    *alpha,
                );

                // Let H = largest_domain;
                // Let H_i = domain;
                // Let v_H := H.vanishing_polynomial();
                // Let v_H_i := H_i.vanishing_polynomial();
                // Let s_i := H.selector_polynomial(H_i) = (v_H / v_H_i) * (H_i.size() / H.size());
                // Let m := masking polynomial
                // Let c_i := circuit combiner
                // Let lhs_i := circuit_specific partial left hand size of the lincheck sumcheck, see protocol docs for more details

                // Instead of just multiplying each lhs_i by `s_i*c_i`, we reorder the lincheck sumcheck to cancel out some terms
                // This removes a mul and div by v_H operation over each circuit's (max_constraint_domain - constraint_domain)

                // Later on, we divide each `lhs_i` and m by v_H, then multiply by `s_i*c_i` and sum them.
                // Substituting in s, we get that:
                // (\sum_i{lhs_i} + m)/v_H = \sum{h_1_i*v_H + x_g_1_i}
                // \sum_i{c_i*s_i*(lhs_i/v_H - x_g_1_i)} + (m/v_H - x_g_1_m) = \sum{h_1_i*v_H}
                // \sum_i{c_i*(H_i.size()/H.size())*(lhs_i/v_H_i - x_g_1_i*v_H/v_H_i)} + (m/v_H - x_g_1_m) = \sum{h_1_i*v_H}
                // \sum_i{c_i*(H_i.size()/H.size())*(lhs_i/v_H_i} + m/v_H = \sum{h_1_i*v_H} + \sum{c_i*x_g_1_i*(v_H/v_H_i)*(H_i.size()/H.size())} + x_g_1_m
                // (\sum_i{c_i*s_i*lhs_i} + m)/v_H = \sum{h_1_i*v_H} + \sum{c_i*s_i*x_g_1_i} + x_g_1_m
                // (\sum_i{c_i*s_i*lhs_i} + m)/v_H = h_1*v_H + x_g_1
                // That's what we're computing here.

                let sumcheck_time = start_timer!(|| format!("Compute sumcheck h and g for {}", _circuit_id));
                let multiplier = circuit_combiner * constraint_domain.size_as_field_element * max_constraint_domain_inv;
                cfg_iter_mut!(circuit_specific_lhs.coeffs).for_each(|c| *c *= multiplier);
                let (h_1_i, mut xg_1_i) = circuit_specific_lhs.divide_by_vanishing_poly(constraint_domain).unwrap();
                xg_1_i = xg_1_i.mul_by_vanishing_poly(max_constraint_domain);
                let (xg_1_i, remainder) = xg_1_i.divide_by_vanishing_poly(constraint_domain).unwrap();
                assert!(remainder.is_zero());
                end_timer!(sumcheck_time);

                (h_1_i, xg_1_i)
            });
        }

        let mut h_1_sum = DensePolynomial::zero();
        let mut xg_1_sum = DensePolynomial::zero();
        for (mut h_1_i, mut xg_1_i) in job_pool.execute_all().into_iter() {
            h_1_sum += &core::mem::take(&mut h_1_i);
            xg_1_sum += &core::mem::take(&mut xg_1_i);
        }

        let mask_poly = state.first_round_oracles.as_ref().unwrap().mask_poly.as_ref();
        assert_eq!(MM::ZK, mask_poly.is_some());
        let mask_poly = &mask_poly.map_or(DensePolynomial::zero(), |p| p.polynomial().into_dense());
        let (mut h_1_mask, mut xg_1_mask) = mask_poly.divide_by_vanishing_poly(max_constraint_domain).unwrap();
        h_1_sum += &core::mem::take(&mut h_1_mask);
        xg_1_sum += &core::mem::take(&mut xg_1_mask);

        (h_1_sum, xg_1_sum)
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
        multiplier.add_evaluation(r_alpha_x_evals, "r_alpha_x"); // we call this u_H(\alpha,X) in the documentation
        let lhs = multiplier
            .element_wise_arithmetic_4_over_domain(mul_domain, ["r_alpha_x", "summed_z_m", "z", "t"], |a, b, c, d| {
                a * b - c * d
            })
            .unwrap();

        end_timer!(q_1_time);
        lhs
    }

    fn calculate_summed_z_m_and_t(
        state: &prover::State<F, MM>,
        alpha: F,
        eta_b: F,
        eta_c: F,
        batch_combiners: &BTreeMap<CircuitId, verifier::BatchCombiners<F>>,
    ) -> Vec<LincheckPoly<F>> {
        let max_constraint_domain = state.max_constraint_domain;
        let first_msg = state.first_round_oracles.as_ref().unwrap();

        assert_eq!(batch_combiners.len(), state.circuit_specific_states.len());
        let mut job_pool = ExecutionPool::with_capacity(2 * state.circuit_specific_states.len());

        for (circuit, circuit_specific_state) in state.circuit_specific_states.iter() {
            let fft_precomputation = &circuit.fft_precomputation;
            let ifft_precomputation = &circuit.ifft_precomputation;
            let eta_b_over_eta_c = eta_b * eta_c.inverse().unwrap();
            let first_msg_i = &first_msg.batches[&circuit.id];
            let instance_combiners = &batch_combiners[&circuit.id].instance_combiners;
            let _circuit_id_z_m = &circuit.id;
            let _circuit_id_t = &circuit.id;
            let circuit_constraint_domain = circuit_specific_state.constraint_domain;
            let circuit_input_domain = circuit_specific_state.input_domain;
            job_pool.add_job(move || {
                let summed_z_m_poly_time =
                    start_timer!(|| format!("Compute z_m poly for circuit {:?}", _circuit_id_z_m));
                let summed_z_m = cfg_iter!(first_msg_i)
                    .zip_eq(instance_combiners)
                    .map(|(entry, combiner)| {
                        let z_a = entry.z_a_poly.polynomial().as_dense().unwrap();
                        let mut z_b = entry.z_b_poly.polynomial().as_dense().unwrap().clone();
                        assert!(z_a.degree() < max_constraint_domain.size());
                        if MM::ZK {
                            assert_eq!(z_b.degree(), circuit_constraint_domain.size());
                        } else {
                            assert!(z_b.degree() < circuit_constraint_domain.size());
                        }

                        // we want to calculate batch_combiner_i * (z_a + eta_b * z_b + eta_c * z_a * z_b);
                        // we rewrite this as batch_combiner_i * (z_a * (eta_c * z_b + 1) + eta_b * z_b);
                        // This is better since it reduces the number of required
                        // multiplications by `circuit_constraint_domain.size()`.
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
                        // Zip safety: `z_b` is smaller than `summed_z_m`.
                        cfg_iter_mut!(summed_z_m.coeffs).zip(&z_b.coeffs).for_each(|(c, b)| *c += eta_b_over_eta_c * b);

                        // Multiply by linear combination coefficient.
                        cfg_iter_mut!(summed_z_m.coeffs).for_each(|c| *c *= combiner);

                        assert_eq!(summed_z_m.degree(), z_a.degree() + z_b.degree());
                        end_timer!(summed_z_m_poly_time);
                        summed_z_m
                    })
                    .sum::<DensePolynomial<_>>();
                LincheckPoly { circuit_id: circuit.id, poly: summed_z_m }
            });

            job_pool.add_job(move || {
                let t_poly_time = start_timer!(|| format!("Compute t poly for circuit {:?}", _circuit_id_t));

                let r_alpha_x_evals =
                    circuit_constraint_domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(alpha);
                let t = Self::calculate_t(
                    &[&circuit.a, &circuit.b, &circuit.c],
                    [F::one(), eta_b, eta_c],
                    &circuit_input_domain,
                    &circuit_constraint_domain,
                    &r_alpha_x_evals,
                    ifft_precomputation,
                );
                end_timer!(t_poly_time);
                LincheckPoly { circuit_id: circuit.id, poly: t }
            });
        }

        job_pool.execute_all()
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
