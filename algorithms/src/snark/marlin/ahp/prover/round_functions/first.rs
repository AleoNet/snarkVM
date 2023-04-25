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
    fft::{DensePolynomial, EvaluationDomain, Evaluations as EvaluationsOnDomain, SparsePolynomial},
    polycommit::sonic_pc::{
        LabeledPolynomial,
        LabeledPolynomialWithBasis,
        PolynomialInfo,
        PolynomialLabel,
        PolynomialWithBasis,
    },
    snark::marlin::{
        ahp::{AHPError, AHPForR1CS},
        prover,
        witness_label,
        Circuit,
        CircuitId,
        MarlinMode,
    },
};
use itertools::Itertools;
use snarkvm_fields::PrimeField;
use snarkvm_utilities::cfg_into_iter;

use rand_core::RngCore;

#[cfg(not(feature = "serial"))]
use rayon::prelude::*;

impl<F: PrimeField, MM: MarlinMode> AHPForR1CS<F, MM> {
    /// Output the number of oracles sent by the prover in the first round.
    pub fn num_first_round_oracles(total_batch_size: usize) -> usize {
        3 * total_batch_size + (MM::ZK as usize)
    }

    /// Output the degree bounds of oracles in the first round.
    pub fn first_round_polynomial_info<'a>(
        circuits: impl Iterator<Item = (&'a CircuitId, &'a usize)>,
    ) -> BTreeMap<PolynomialLabel, PolynomialInfo> {
        let mut polynomials = circuits
            .flat_map(|(&circuit_id, &batch_size)| {
                (0..batch_size).flat_map(move |i| {
                    [
                        PolynomialInfo::new(witness_label(circuit_id, "w", i), None, Self::zk_bound()),
                        PolynomialInfo::new(witness_label(circuit_id, "z_a", i), None, Self::zk_bound()),
                        PolynomialInfo::new(witness_label(circuit_id, "z_b", i), None, Self::zk_bound()),
                    ]
                })
            })
            .collect::<Vec<_>>();
        if MM::ZK {
            polynomials.push(PolynomialInfo::new("mask_poly".to_string(), None, None));
        }
        polynomials.into_iter().map(|info| (info.label().into(), info)).collect()
    }

    /// Output the first round message and the next state.
    #[allow(clippy::type_complexity)]
    pub fn prover_first_round<'a, R: RngCore>(
        mut state: prover::State<'a, F, MM>,
        rng: &mut R,
    ) -> Result<prover::State<'a, F, MM>, AHPError> {
        let round_time = start_timer!(|| "AHP::Prover::FirstRound");
        let mut r_b_s = Vec::with_capacity(state.circuit_specific_states.len());
        let mut job_pool = snarkvm_utilities::ExecutionPool::with_capacity(3 * state.total_instances);
        for (circuit, circuit_state) in state.circuit_specific_states.iter_mut() {
            let batch_size = circuit_state.batch_size;

            let z_a = circuit_state.z_a.take().unwrap();
            let z_b = circuit_state.z_b.take().unwrap();
            let private_variables = core::mem::take(&mut circuit_state.private_variables);
            let x_polys = circuit_state.x_polys.clone();
            assert_eq!(z_a.len(), batch_size);
            assert_eq!(z_b.len(), batch_size);
            assert_eq!(private_variables.len(), batch_size);
            assert_eq!(x_polys.len(), batch_size);

            let c_domain = circuit_state.constraint_domain;
            let i_domain = circuit_state.input_domain;

            let mut circuit_r_b_s = Vec::with_capacity(batch_size);
            for (j, (z_a, z_b, private_vars, x_poly)) in
                itertools::izip!(z_a, z_b, private_variables, x_polys).enumerate()
            {
                let w_label = witness_label(circuit.id, "w", j);
                let za_label = witness_label(circuit.id, "z_a", j);
                let zb_label = witness_label(circuit.id, "z_b", j);
                job_pool.add_job(move || Self::calc_w(w_label, private_vars, x_poly, c_domain, i_domain, circuit));
                job_pool.add_job(move || Self::calc_z_m(za_label, z_a, c_domain, circuit, None));
                let r_b = F::rand(rng);
                job_pool.add_job(move || Self::calc_z_m(zb_label, z_b, c_domain, circuit, Some(r_b)));
                if MM::ZK {
                    circuit_r_b_s.push(r_b);
                }
            }
            r_b_s.push(circuit_r_b_s);
        }
        let mut batches = job_pool
            .execute_all()
            .into_iter()
            .tuples()
            .map(|(w, z_a, z_b)| {
                let w_poly = w.witness().unwrap();
                let (z_a_poly, z_a) = z_a.z_m().unwrap();
                let (z_b_poly, z_b) = z_b.z_m().unwrap();

                prover::SingleEntry { z_a, z_b, w_poly, z_a_poly, z_b_poly }
            })
            .collect::<Vec<_>>();
        assert_eq!(batches.len(), state.total_instances);

        let mut circuit_specific_batches = BTreeMap::new();
        for ((circuit, state), r_b_s) in state.circuit_specific_states.iter_mut().zip(r_b_s) {
            let batches = batches.drain(0..state.batch_size).collect_vec();
            circuit_specific_batches.insert(circuit.id, batches);
            state.mz_poly_randomizer = MM::ZK.then_some(r_b_s);
            end_timer!(round_time);
        }
        let mask_poly = Self::calculate_mask_poly(state.max_constraint_domain, rng);
        let oracles = prover::FirstOracles { batches: circuit_specific_batches, mask_poly };
        assert!(oracles.matches_info(&Self::first_round_polynomial_info(
            state.circuit_specific_states.iter().map(|(c, s)| (&c.id, &s.batch_size))
        )));
        state.first_round_oracles = Some(Arc::new(oracles));
        Ok(state)
    }

    fn calculate_mask_poly<R: RngCore>(
        constraint_domain: EvaluationDomain<F>,
        rng: &mut R,
    ) -> Option<LabeledPolynomial<F>> {
        MM::ZK
            .then(|| {
                let mask_poly_time = start_timer!(|| "Computing mask polynomial");
                // We'll use the masking technique from Lunar (https://eprint.iacr.org/2020/1069.pdf, pgs 20-22).
                let h_1_mask = DensePolynomial::rand(3, rng).coeffs; // selected arbitrarily.
                let h_1_mask = SparsePolynomial::from_coefficients(h_1_mask.into_iter().enumerate())
                    .mul(&constraint_domain.vanishing_polynomial());
                assert_eq!(h_1_mask.degree(), constraint_domain.size() + 3);
                // multiply g_1_mask by X
                let mut g_1_mask = DensePolynomial::rand(5, rng);
                g_1_mask.coeffs[0] = F::zero();
                let g_1_mask = SparsePolynomial::from_coefficients(
                    g_1_mask.coeffs.into_iter().enumerate().filter(|(_, coeff)| !coeff.is_zero()),
                );

                let mut mask_poly = h_1_mask;
                mask_poly += &g_1_mask;
                debug_assert!(constraint_domain.elements().map(|z| mask_poly.evaluate(z)).sum::<F>().is_zero());
                assert_eq!(mask_poly.degree(), constraint_domain.size() + 3);
                assert!(mask_poly.degree() <= 3 * constraint_domain.size() + 2 * Self::zk_bound().unwrap() - 3);

                end_timer!(mask_poly_time);
                mask_poly
            })
            .map(|mask_poly| LabeledPolynomial::new("mask_poly".to_string(), mask_poly, None, None))
    }

    fn calc_w(
        label: String,
        private_variables: Vec<F>,
        x_poly: DensePolynomial<F>,
        constraint_domain: EvaluationDomain<F>,
        input_domain: EvaluationDomain<F>,
        circuit: &Circuit<F, MM>,
    ) -> PoolResult<F> {
        let mut w_extended = private_variables;
        let ratio = constraint_domain.size() / input_domain.size();
        w_extended.resize(constraint_domain.size() - input_domain.size(), F::zero());

        let x_evals = {
            let mut coeffs = x_poly.coeffs;
            coeffs.resize(constraint_domain.size(), F::zero());
            constraint_domain.in_order_fft_in_place_with_pc(&mut coeffs, &circuit.fft_precomputation);
            coeffs
        };

        let w_poly_time = start_timer!(|| "Computing w polynomial");
        let w_poly_evals = cfg_into_iter!(0..constraint_domain.size())
            .map(|k| match k % ratio {
                0 => F::zero(),
                _ => w_extended[k - (k / ratio) - 1] - x_evals[k],
            })
            .collect();
        let w_poly = EvaluationsOnDomain::from_vec_and_domain(w_poly_evals, constraint_domain)
            .interpolate_with_pc(&circuit.ifft_precomputation);
        let (w_poly, remainder) = w_poly.divide_by_vanishing_poly(input_domain).unwrap();
        assert!(remainder.is_zero());

        assert!(w_poly.degree() < constraint_domain.size() - input_domain.size());
        end_timer!(w_poly_time);
        PoolResult::Witness(LabeledPolynomial::new(label, w_poly, None, Self::zk_bound()))
    }

    fn calc_z_m(
        label: impl ToString,
        evaluations: Vec<F>,
        constraint_domain: EvaluationDomain<F>,
        circuit: &Circuit<F, MM>,
        r: Option<F>,
    ) -> PoolResult<F> {
        let should_randomize = MM::ZK && r.is_some();
        let v_H = constraint_domain.vanishing_polynomial();
        let label = label.to_string();
        let poly_time = start_timer!(|| format!("Computing {label}"));

        let evals = EvaluationsOnDomain::from_vec_and_domain(evaluations, constraint_domain);

        let mut poly = evals.interpolate_with_pc_by_ref(&circuit.ifft_precomputation);
        if should_randomize {
            poly += &(&v_H * r.unwrap());
        }

        debug_assert!(
            poly.evaluate_over_domain_by_ref(constraint_domain)
                .evaluations
                .into_iter()
                .zip(&evals.evaluations)
                .all(|(z, e)| *e == z),
            "Label: {label}\n1: {:#?}\n2: {:#?}",
            poly.evaluate_over_domain_by_ref(constraint_domain).evaluations,
            &evals.evaluations,
        );

        let poly_for_opening = LabeledPolynomial::new(label.to_string(), poly, None, Self::zk_bound());
        if should_randomize {
            assert!(poly_for_opening.degree() < constraint_domain.size() + Self::zk_bound().unwrap());
        } else {
            assert!(poly_for_opening.degree() < constraint_domain.size());
        }

        let poly_for_committing = if should_randomize {
            let poly_terms = vec![
                (F::one(), PolynomialWithBasis::new_lagrange_basis(evals)),
                (F::one(), PolynomialWithBasis::new_sparse_monomial_basis(&v_H * r.unwrap(), None)),
            ];
            LabeledPolynomialWithBasis::new_linear_combination(label, poly_terms, Self::zk_bound())
        } else {
            LabeledPolynomialWithBasis::new_lagrange_basis(label, evals, Self::zk_bound())
        };
        end_timer!(poly_time);

        PoolResult::MatrixPoly(poly_for_opening, poly_for_committing)
    }
}

#[derive(Debug)]
pub enum PoolResult<F: PrimeField> {
    Witness(LabeledPolynomial<F>),
    MatrixPoly(LabeledPolynomial<F>, LabeledPolynomialWithBasis<'static, F>),
}

impl<F: PrimeField> PoolResult<F> {
    fn witness(self) -> Option<LabeledPolynomial<F>> {
        match self {
            Self::Witness(poly) => Some(poly),
            _ => None,
        }
    }

    fn z_m(self) -> Option<(LabeledPolynomial<F>, LabeledPolynomialWithBasis<'static, F>)> {
        match self {
            Self::MatrixPoly(p1, p2) => Some((p1, p2)),
            _ => None,
        }
    }
}
