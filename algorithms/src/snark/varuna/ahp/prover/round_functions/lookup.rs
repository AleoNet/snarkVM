// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

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
    snark::varuna::{
        ahp::{verifier, AHPError, AHPForR1CS, CircuitId},
        prover,
        witness_label,
        CircuitInfo,
        SNARKMode,
    },
};
use snarkvm_fields::{batch_inversion_and_mul, PrimeField};
use snarkvm_utilities::{cfg_iter, cfg_iter_mut, ExecutionPool};

use anyhow::{ensure, Result};
use itertools::Itertools;
use rand_core::RngCore;

#[cfg(not(feature = "serial"))]
use rayon::prelude::*;

type Sum<F> = F;
type Lhs<F> = DensePolynomial<F>;
type Gpoly<F> = LabeledPolynomial<F>;

impl<F: PrimeField, MM: SNARKMode> AHPForR1CS<F, MM> {
    /// Output the number of oracles sent by the prover
    pub fn num_lookup_round_oracles(instances: usize) -> usize {
        instances
    }

    /// Output the degree bounds of oracles
    pub fn lookup_round_polynomial_info<'a>(
        batch_sizes: impl Iterator<Item = ((CircuitId, &'a CircuitInfo), &'a usize)>,
    ) -> BTreeMap<PolynomialLabel, PolynomialInfo> {
        let polynomials = batch_sizes
            .flat_map(|((circuit_id, &info), &batch_size)| {
                // TODO: double check bounds of new polys
                let constraint_size = EvaluationDomain::<F>::compute_size_of_domain(info.num_constraints).unwrap();
                (0..batch_size).flat_map(move |j| {
                    [PolynomialInfo::new(witness_label(circuit_id, "g_0", j), Some(constraint_size - 2), None)]
                })
            })
            .collect::<Vec<_>>();
        polynomials.into_iter().map(|info| (info.label().into(), info)).collect()
    }

    /// Output the lookup round message and the next state.
    pub fn prover_lookup_round<'a, R: RngCore>(
        first_message: &verifier::FirstMessage<F>,
        mut state: prover::State<'a, F, MM>,
        _r: &mut R,
    ) -> Result<(prover::LookupOracles<F>, prover::State<'a, F, MM>), AHPError> {
        let round_time = start_timer!(|| "AHP::Prover::LookupRound");

        let verifier::FirstMessage { zeta, theta, .. } = first_message;
        let zeta_squared = *zeta * *zeta;

        let num_lookup_instances = state
            .circuit_specific_states
            .iter()
            .filter(|(&c, _)| c.table_info.is_some())
            .map(|(_, s)| s.batch_size)
            .sum();

        // TODO: move to its own function
        let (s_lookup_evals, t_theta_evals, t_theta_polys): (Vec<Vec<F>>, Vec<Vec<F>>, Vec<DensePolynomial<F>>) = state
            .circuit_specific_states
            .iter_mut()
            .filter(|(&c, _)| c.table_info.is_some())
            .map(|(circuit, state_i)| {
                let constraint_domain = state_i.constraint_domain;
                let s_lookup_evals = circuit.s_lookup_evals.as_ref().unwrap();
                let mut s_lookup_evals_i = Vec::with_capacity(constraint_domain.size());
                s_lookup_evals_i.extend(s_lookup_evals.iter());
                s_lookup_evals_i.resize(constraint_domain.size(), F::zero());

                let mut t_evals = circuit
                    .table_info
                    .as_ref()
                    .unwrap()
                    .lookup_tables
                    .iter()
                    .flat_map(|table| {
                        table
                            .table
                            .iter()
                            .map(|(key, value)| key[0] + *zeta * key[1] + zeta_squared * value)
                            .collect::<Vec<F>>()
                    })
                    .collect::<Vec<F>>();
                t_evals.resize(circuit.index_info.num_constraints, t_evals[0]);
                cfg_iter_mut!(t_evals).for_each(|t| *t += *theta);
                t_evals.resize(constraint_domain.size(), *theta);
                let t_theta_poly = EvaluationsOnDomain::from_vec_and_domain(t_evals.clone(), constraint_domain)
                    .interpolate_with_pc(&circuit.ifft_precomputation);

                (s_lookup_evals_i, t_evals, t_theta_poly)
            })
            .multiunzip();

        let mut pool = ExecutionPool::with_capacity(num_lookup_instances);

        // Only iterate over circuits which actually use lookups
        for ((((&circuit, state_i), s_lookup_evals_i), t_theta_evals_i), t_theta_poly) in state
            .circuit_specific_states
            .iter_mut()
            .filter(|(&c, _)| c.table_info.is_some())
            .zip_eq(s_lookup_evals.iter())
            .zip_eq(t_theta_evals.iter())
            .zip_eq(t_theta_polys.iter())
        {
            let constraint_domain = state_i.constraint_domain;
            let z_a = state_i.z_a.as_ref().unwrap();
            let z_b = state_i.z_b.as_ref().unwrap();
            let z_c = state_i.z_c.as_ref().unwrap();
            let m_evals = state_i.m_evals.take().unwrap_or(vec![vec![]; state_i.batch_size]);
            let first_oracles = state.first_round_oracles.as_ref().unwrap().batches.get(&circuit.id).unwrap();
            let s_lookup_poly = circuit.s_lookup.as_ref().unwrap().polynomial().as_dense().unwrap();

            for (j, ((((mut m_evals_j, z_a), z_b), z_c), first_oracle)) in
                m_evals.into_iter().zip_eq(z_a).zip_eq(z_b).zip_eq(z_c).zip_eq(first_oracles).enumerate()
            {
                let mut f_evals = cfg_iter!(z_a)
                    .zip_eq(z_b)
                    .zip_eq(z_c)
                    .map(|((&a, &b), &c)| a + *zeta * b + zeta_squared * c)
                    .collect::<Vec<F>>();

                let label = witness_label(circuit.id, "g_0", j);
                m_evals_j.resize(constraint_domain.size(), F::zero());
                f_evals.resize(constraint_domain.size(), F::zero());
                let m_poly_j = first_oracle.multiplicities.as_ref().unwrap().polynomial().as_dense().unwrap();
                pool.add_job(move || {
                    let result = Self::lookup_sumcheck_helper(
                        label,
                        constraint_domain,
                        *theta,
                        t_theta_evals_i,
                        t_theta_poly,
                        m_evals_j,
                        m_poly_j,
                        f_evals,
                        s_lookup_evals_i,
                        s_lookup_poly,
                        &circuit.fft_precomputation,
                        &circuit.ifft_precomputation,
                    );
                    (circuit, result)
                });
            }
        }

        let mut gs = BTreeMap::new();
        for (circuit, result) in pool.execute_all().into_iter() {
            let batch_size = state.circuit_specific_states.get(&circuit).unwrap().batch_size;
            let (sum, h, g) = result?;
            assert!(sum.is_zero(), "we expect the lookup polys to sum to 0");
            gs.entry(circuit.id).or_insert(Vec::with_capacity(batch_size)).push(g);
            let mut lookup_h_polynomials = state
                .circuit_specific_states
                .get_mut(&circuit)
                .unwrap()
                .lookup_h_polynomials
                .take()
                .unwrap_or(Vec::with_capacity(batch_size));
            lookup_h_polynomials.push(h);
            state.circuit_specific_states.get_mut(&circuit).unwrap().lookup_h_polynomials = Some(lookup_h_polynomials);
        }

        let oracles = prover::LookupOracles { gs };

        assert!(oracles.matches_info(&Self::lookup_round_polynomial_info(
            state.circuit_specific_states.iter().map(|(c, s)| ((c.id, &c.index_info), &s.batch_size))
        )));

        end_timer!(round_time);

        Ok((oracles, state))
    }

    #[allow(clippy::too_many_arguments)]
    fn lookup_sumcheck_helper(
        label: String,
        constraint_domain: EvaluationDomain<F>,
        theta: F,
        t_theta_evals: &Vec<F>,
        t_theta_poly: &DensePolynomial<F>,
        m_evals: Vec<F>,
        m_poly: &DensePolynomial<F>,
        f_evals: Vec<F>,
        s_lookup_evals: &Vec<F>,
        s_lookup_poly: &DensePolynomial<F>,
        fft_precomputation: &FFTPrecomputation<F>,
        ifft_precomputation: &IFFTPrecomputation<F>,
    ) -> Result<(Sum<F>, Lhs<F>, Gpoly<F>)> {
        // TODO: profile and optimize, consider computing directly on evaluations
        let lookup_time = start_timer!(|| format!("lookup_sumcheck_helper {}", label));

        let evals: Vec<F> = cfg_iter!(&f_evals).map(|f| theta + f).collect();
        let lookup_theta =
            EvaluationsOnDomain::from_vec_and_domain(evals, constraint_domain).interpolate_with_pc(ifft_precomputation);

        let mut multiplier = PolyMultiplier::new();
        multiplier.add_precomputation(fft_precomputation, ifft_precomputation);
        multiplier.add_polynomial_ref(&lookup_theta, "lookup_theta");
        multiplier.add_polynomial_ref(m_poly, "m_poly");
        let mut mult_a = multiplier.multiply().unwrap();
        let mut multiplier = PolyMultiplier::new();
        multiplier.add_precomputation(fft_precomputation, ifft_precomputation);
        multiplier.add_polynomial_ref(t_theta_poly, "table_theta");
        multiplier.add_polynomial_ref(s_lookup_poly, "s_lookup");
        let mult_a_2 = multiplier.multiply().unwrap();
        mult_a -= &mult_a_2;
        let a_poly = mult_a;

        let f_evals_time = start_timer!(|| format!("Computing f evals on K for {label}"));
        let mut inverses: Vec<_> =
            cfg_iter!(&f_evals).zip_eq(t_theta_evals).map(|(&f, &tt)| tt * (theta + f)).collect();

        let new_constant = F::one();
        batch_inversion_and_mul(&mut inverses, &new_constant);

        cfg_iter_mut!(inverses)
            .zip_eq(m_evals)
            .zip_eq(f_evals)
            .zip_eq(t_theta_evals)
            .zip_eq(s_lookup_evals)
            .for_each(|((((inv, m), f), &tt), &s_l)| *inv *= m * (theta + f) - s_l * tt);
        let f_evals_on_R = inverses;

        end_timer!(f_evals_time);

        let f_poly_time = start_timer!(|| format!("Computing f poly for {label}"));
        // we define f as the rational equation for which we're running the sumcheck protocol
        let f = EvaluationsOnDomain::from_vec_and_domain(f_evals_on_R, constraint_domain)
            .interpolate_with_pc(ifft_precomputation);
        let sum = f.coeffs[0];

        ensure!(f.degree() > 0); // No actual lookups are used.

        end_timer!(f_poly_time);
        let g = DensePolynomial::from_coefficients_slice(&f.coeffs[1..]);
        let h = &a_poly
            - &{
                let mut multiplier = PolyMultiplier::new();
                multiplier.add_polynomial(f, "f");
                multiplier.add_polynomial_ref(t_theta_poly, "table_theta");
                multiplier.add_polynomial(lookup_theta, "lookup_theta");
                multiplier.add_precomputation(fft_precomputation, ifft_precomputation);
                multiplier.multiply().unwrap()
            };

        let g = LabeledPolynomial::new(label, g, Some(constraint_domain.size() - 2), None);
        end_timer!(lookup_time);

        assert!(h.degree() <= 3 * constraint_domain.size() - 2);
        assert!(g.degree() <= constraint_domain.size() - 2);
        Ok((sum, h, g))
    }
}
