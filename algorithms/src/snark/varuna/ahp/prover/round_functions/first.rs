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

use std::{collections::BTreeMap, sync::Arc};

use crate::{
    fft::{domain::IFFTPrecomputation, DensePolynomial, EvaluationDomain, Evaluations as EvaluationsOnDomain},
    polycommit::sonic_pc::{LabeledPolynomial, PolynomialInfo, PolynomialLabel},
    snark::varuna::{
        ahp::{AHPError, AHPForR1CS},
        prover,
        witness_label,
        Circuit,
        CircuitId,
        SNARKMode,
    },
};
use itertools::Itertools;
use rand_core::RngCore;
use snarkvm_fields::PrimeField;
use snarkvm_utilities::cfg_into_iter;

#[cfg(not(feature = "serial"))]
use rayon::prelude::*;

impl<F: PrimeField, MM: SNARKMode> AHPForR1CS<F, MM> {
    /// Output the number of oracles sent by the prover in the first round.
    pub fn num_first_round_oracles(total_batch_size: usize, total_lookups: usize) -> usize {
        total_batch_size + total_lookups
    }

    /// Output the degree bounds of oracles in the first round.
    pub fn first_round_polynomial_info(
        batch_sizes: impl Iterator<Item = (CircuitId, usize, bool)>,
    ) -> BTreeMap<PolynomialLabel, PolynomialInfo> {
        batch_sizes
            .flat_map(|(circuit_id, batch_size, lookups_used)| {
                (0..batch_size).flat_map(move |i| {
                    [PolynomialInfo::new(witness_label(circuit_id, "w", i), None, Self::zk_bound())].into_iter().chain(
                        lookups_used.then(|| {
                            PolynomialInfo::new(witness_label(circuit_id, "multiplicities", i), None, Self::zk_bound())
                        }),
                    )
                })
            })
            .map(|info| (info.label().into(), info))
            .collect()
    }

    /// Output the first round message and the next state.
    #[allow(clippy::type_complexity)]
    pub fn prover_first_round<'a, R: RngCore>(
        mut state: prover::State<'a, F, MM>,
        rng: &mut R,
    ) -> Result<prover::State<'a, F, MM>, AHPError> {
        let round_time = start_timer!(|| "AHP::Prover::FirstRound");

        let mut job_pool = snarkvm_utilities::ExecutionPool::with_capacity(state.total_instances);
        let mut r_m_s = Vec::with_capacity(state.circuit_specific_states.len());
        for (&circuit, circuit_state) in state.circuit_specific_states.iter_mut() {
            let batch_size = circuit_state.batch_size;

            let private_variables = core::mem::take(&mut circuit_state.private_variables);
            let x_polys = circuit_state.x_polys.clone();
            assert_eq!(private_variables.len(), batch_size);
            assert_eq!(x_polys.len(), batch_size);

            let c_domain = circuit_state.constraint_domain;
            let v_domain = circuit_state.variable_domain;
            let i_domain = circuit_state.input_domain;
            // We clone m_evals because we also need them in the next round
            let m_evals = circuit_state.m_evals.clone().take().unwrap_or(vec![vec![]; batch_size]);
            let ifft = &circuit.ifft_precomputation;

            let mut circuit_r_m_s = Vec::with_capacity(batch_size);
            for (j, ((private_vars, x_poly), m_evals_j)) in
                private_variables.into_iter().zip_eq(x_polys).zip_eq(m_evals).enumerate()
            {
                let r_m = F::rand(rng);
                let m_label = witness_label(circuit.id, "multiplicities", j);
                job_pool.add_job(move || {
                    Self::calc_multiplicities(m_label, m_evals_j, c_domain, ifft, MM::ZK.then_some(r_m))
                });
                let w_label = witness_label(circuit.id, "w", j);
                job_pool.add_job(move || Self::calculate_w(w_label, private_vars, x_poly, v_domain, i_domain, circuit));
                circuit_r_m_s.push(r_m);
            }
            r_m_s.push(circuit_r_m_s);
        }
        let mut batches = job_pool
            .execute_all()
            .into_iter()
            .tuples()
            .map(|(multiplicities, w_poly)| prover::SingleEntry { multiplicities, w_poly: w_poly.unwrap() })
            .collect::<Vec<_>>();
        assert_eq!(batches.len(), state.total_instances);

        let mut circuit_specific_batches = BTreeMap::new();
        for ((circuit, state_i), r_m_s) in state.circuit_specific_states.iter_mut().zip_eq(r_m_s) {
            let batches = batches.drain(0..state_i.batch_size).collect_vec();
            circuit_specific_batches.insert(circuit.id, batches);
            state_i.multiplicity_randomizer = MM::ZK.then_some(r_m_s);
        }
        let oracles = prover::FirstOracles { batches: circuit_specific_batches };
        assert!(oracles.matches_info(&Self::first_round_polynomial_info(
            state.circuit_specific_states.iter().map(|(c, s)| (c.id, s.batch_size, s.m_evals.is_some()))
        )));
        state.first_round_oracles = Some(Arc::new(oracles));
        end_timer!(round_time);
        Ok(state)
    }

    fn calculate_w(
        label: String,
        private_variables: Vec<F>,
        x_poly: DensePolynomial<F>,
        variable_domain: EvaluationDomain<F>,
        input_domain: EvaluationDomain<F>,
        circuit: &Circuit<F, MM>,
    ) -> Option<LabeledPolynomial<F>> {
        let mut w_extended = private_variables;
        let ratio = variable_domain.size() / input_domain.size();
        w_extended.resize(variable_domain.size() - input_domain.size(), F::zero());

        let x_evals = {
            let mut coeffs = x_poly.coeffs;
            coeffs.resize(variable_domain.size(), F::zero());
            variable_domain.in_order_fft_in_place_with_pc(&mut coeffs, &circuit.fft_precomputation);
            coeffs
        };

        let w_poly_time = start_timer!(|| "Computing w polynomial");
        let w_poly_evals = cfg_into_iter!(0..variable_domain.size())
            .map(|k| match k % ratio {
                0 => F::zero(),
                _ => w_extended[k - (k / ratio) - 1] - x_evals[k],
            })
            .collect();
        let w_poly = EvaluationsOnDomain::from_vec_and_domain(w_poly_evals, variable_domain)
            .interpolate_with_pc(&circuit.ifft_precomputation);
        let (w_poly, remainder) = w_poly.divide_by_vanishing_poly(input_domain).unwrap();
        assert!(remainder.is_zero());

        assert!(w_poly.degree() < variable_domain.size() - input_domain.size());
        end_timer!(w_poly_time);
        Some(LabeledPolynomial::new(label, w_poly, None, Self::zk_bound()))
    }

    fn calc_multiplicities(
        label: String,
        m_evals: Vec<F>,
        c_domain: EvaluationDomain<F>,
        ifft_precomputation: &IFFTPrecomputation<F>,
        r_m: Option<F>,
    ) -> Option<LabeledPolynomial<F>> {
        if m_evals.is_empty() {
            return None;
        }

        let m_poly_time = start_timer!(|| "Computing multiplicity poly");
        let mut m_poly =
            EvaluationsOnDomain::from_vec_and_domain(m_evals, c_domain).interpolate_with_pc(ifft_precomputation);

        if let Some(r_m) = r_m {
            let v_H = c_domain.vanishing_polynomial();
            m_poly += &(&v_H * r_m);
        }
        end_timer!(m_poly_time);

        Some(LabeledPolynomial::new(label, m_poly, None, Self::zk_bound()))
    }
}
