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
        MarlinMode,
    },
};
use itertools::Itertools;
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{cfg_into_iter, cfg_iter};

use rand_core::RngCore;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

impl<F: PrimeField, MM: MarlinMode> AHPForR1CS<F, MM> {
    /// Output the number of oracles sent by the prover in the first round.
    pub fn num_first_round_oracles(batch_size: usize) -> usize {
        8 * batch_size + (MM::ZK as usize)
    }

    /// Output the degree bounds of oracles in the first round.
    pub fn first_round_polynomial_info(batch_size: usize) -> BTreeMap<PolynomialLabel, PolynomialInfo> {
        let mut polynomials = Vec::new();

        for i in 0..batch_size {
            polynomials.push(PolynomialInfo::new(witness_label("w", i), None, Self::zk_bound()));
            polynomials.push(PolynomialInfo::new(witness_label("z_a", i), None, Self::zk_bound()));
            polynomials.push(PolynomialInfo::new(witness_label("z_b", i), None, Self::zk_bound()));
            polynomials.push(PolynomialInfo::new(witness_label("z_c", i), None, Self::zk_bound()));
            polynomials.push(PolynomialInfo::new(witness_label("f", i), None, Self::zk_bound()));
            polynomials.push(PolynomialInfo::new(witness_label("s_1", i), None, Self::zk_bound()));
            polynomials.push(PolynomialInfo::new(witness_label("s_2", i), None, Self::zk_bound()));
            polynomials.push(PolynomialInfo::new(witness_label("z_2", i), None, Self::zk_bound()));
        }
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
        let constraint_domain = state.constraint_domain;
        let batch_size = state.batch_size;

        let z_a = state.z_a.take().unwrap();
        let z_b = state.z_b.take().unwrap();
        let z_c = state.z_c.take().unwrap();
        let private_variables = core::mem::take(&mut state.private_variables);
        assert_eq!(z_a.len(), batch_size);
        assert_eq!(z_b.len(), batch_size);
        assert_eq!(private_variables.len(), batch_size);
        let mut r_b_s = Vec::with_capacity(batch_size);

        let mut job_pool = snarkvm_utilities::ExecutionPool::with_capacity(3 * batch_size);
        let state_ref = &state;
        for (i, (z_a, z_b, z_c, private_variables, x_poly)) in
            itertools::izip!(&z_a, &z_b, &z_c, private_variables, &state.x_poly).enumerate()
        {
            job_pool.add_job(move || Self::calculate_w(witness_label("w", i), private_variables, x_poly, state_ref));
            job_pool.add_job(move || Self::calculate_z_m(witness_label("z_a", i), z_a, false, state_ref, None));
            let r_b = F::rand(rng);
            job_pool.add_job(move || Self::calculate_z_m(witness_label("z_b", i), z_b, true, state_ref, Some(r_b)));
            if MM::ZK {
                r_b_s.push(r_b);
            }
            job_pool.add_job(move || Self::calculate_z_m(witness_label("z_c", i), z_c, true, state_ref, Some(r_b)));
            job_pool.add_job(move || {
                Self::calculate_table_polys(
                    witness_label("f", i),
                    witness_label("s_1", i),
                    witness_label("s_2", i),
                    witness_label("z_2", i),
                    z_a,
                    z_b,
                    z_c,
                    &state.index.s_l_evals,
                    true,
                    state_ref,
                    Some(r_b),
                )
            });
        }

        let batches = job_pool
            .execute_all()
            .into_iter()
            .tuples()
            .map(|(w, z_a, z_b, z_c, table_polys)| {
                let w_poly = w.witness().unwrap();
                let (z_a_poly, z_a) = z_a.z_m().unwrap();
                let (z_b_poly, z_b) = z_b.z_m().unwrap();
                let (z_c_poly, z_c) = z_c.z_m().unwrap();
                let table_polys = table_polys.table_polys().unwrap();

                // TODO: can we avoid the excessive cloning related to table_polys?
                state.plookup_evals.push([
                    table_polys[0].2.clone(),
                    table_polys[1].2.clone(),
                    table_polys[2].2.clone(),
                    table_polys[3].2.clone(),
                ]);

                prover::SingleEntry {
                    z_a,
                    z_b,
                    z_c,
                    f: table_polys[0].1.clone(),
                    s_1: table_polys[1].1.clone(),
                    s_2: table_polys[2].1.clone(),
                    z_2: table_polys[3].1.clone(),
                    w_poly,
                    z_a_poly,
                    z_b_poly,
                    z_c_poly,
                    f_poly: table_polys[0].0.clone(),
                    s_1_poly: table_polys[1].0.clone(),
                    s_2_poly: table_polys[2].0.clone(),
                    z_2_poly: table_polys[3].0.clone(),
                }
            })
            .collect::<Vec<_>>();
        assert_eq!(batches.len(), batch_size);

        let mask_poly = Self::calculate_mask_poly(constraint_domain, rng);

        let oracles = prover::FirstOracles { batches, mask_poly };
        assert!(oracles.matches_info(&Self::first_round_polynomial_info(batch_size)));
        state.first_round_oracles = Some(Arc::new(oracles));
        state.mz_poly_randomizer = MM::ZK.then(|| r_b_s);
        end_timer!(round_time);

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

    fn calculate_w<'a>(
        label: String,
        private_variables: Vec<F>,
        x_poly: &DensePolynomial<F>,
        state: &prover::State<'a, F, MM>,
    ) -> PoolResult<'a, F> {
        let constraint_domain = state.constraint_domain;
        let input_domain = state.input_domain;

        let mut w_extended = private_variables;
        let ratio = constraint_domain.size() / input_domain.size();
        w_extended.resize(constraint_domain.size() - input_domain.size(), F::zero());

        let x_evals = {
            let mut coeffs = x_poly.coeffs.clone();
            coeffs.resize(constraint_domain.size(), F::zero());
            constraint_domain.in_order_fft_in_place_with_pc(&mut coeffs, state.fft_precomputation());
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
            .interpolate_with_pc(state.ifft_precomputation());
        let (w_poly, remainder) = w_poly.divide_by_vanishing_poly(input_domain).unwrap();
        assert!(remainder.is_zero());

        assert!(w_poly.degree() < constraint_domain.size() - input_domain.size());
        end_timer!(w_poly_time);
        PoolResult::Witness(LabeledPolynomial::new(label, w_poly, None, Self::zk_bound()))
    }

    fn calculate_z_m<'a>(
        label: impl ToString,
        evaluations: &[F],
        will_be_evaluated: bool,
        state: &prover::State<'a, F, MM>,
        r: Option<F>,
    ) -> PoolResult<'a, F> {
        let (poly_for_opening, poly_for_committing) =
            Self::calculate_opening_and_commitment_polys(label, evaluations, will_be_evaluated, state, r);
        PoolResult::MatrixPoly(poly_for_opening, poly_for_committing)
    }

    fn calculate_opening_and_commitment_polys<'a>(
        label: impl ToString,
        evaluations: &[F],
        will_be_evaluated: bool,
        state: &prover::State<'a, F, MM>,
        r: Option<F>,
    ) -> (LabeledPolynomial<F>, LabeledPolynomialWithBasis<'a, F>) {
        let constraint_domain = state.constraint_domain;
        let v_H = constraint_domain.vanishing_polynomial();
        let should_randomize = MM::ZK && will_be_evaluated;
        let label = label.to_string();
        let poly_time = start_timer!(|| format!("Computing {label}"));

        let evals = EvaluationsOnDomain::from_vec_and_domain(evaluations.to_vec(), constraint_domain);

        let mut poly = evals.interpolate_with_pc_by_ref(state.ifft_precomputation());
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

        (poly_for_opening, poly_for_committing)
    }

    #[allow(clippy::too_many_arguments)]
    fn calculate_table_polys<'a>(
        label_f: impl ToString,
        label_s_1: impl ToString,
        label_s_2: impl ToString,
        label_z_2: impl ToString,
        z_a: &[F],
        z_b: &[F],
        z_c: &[F],
        s_l: &[F],
        will_be_evaluated: bool,
        state: &prover::State<'a, F, MM>,
        r: Option<F>,
    ) -> PoolResult<'a, F> {
        let constraint_domain = state.constraint_domain;
        let zeta_squared = state.index.zeta.square();
        let f_evals = cfg_iter!(z_a)
            .zip(z_b)
            .zip(z_c)
            .zip(s_l)
            .map(|(((a, b), c), s)| {
                if s.is_zero() {
                    state.index.t_evals[state.index.t_evals.len() - 1]
                } else {
                    *a + state.index.zeta * b + zeta_squared * c
                }
            })
            .collect::<Vec<F>>();

        let f = Self::calculate_opening_and_commitment_polys(label_f, &f_evals, will_be_evaluated, state, r);
        let mut s_evals = f_evals.clone();
        s_evals.extend(state.index.t_evals.clone());
        // Split into alternating halves.
        let (s_1_evals, s_2_evals): (Vec<F>, Vec<F>) = s_evals.chunks(2).map(|els| (els[0], els[1])).unzip();
        let s_1 = Self::calculate_opening_and_commitment_polys(label_s_1, &s_1_evals, will_be_evaluated, state, r);
        let s_2 = Self::calculate_opening_and_commitment_polys(label_s_2, &s_2_evals, will_be_evaluated, state, r);

        // Calculate z_2
        // Compute divisions for each constraint
        let product_arguments = f_evals
            .iter()
            .enumerate()
            .zip(&state.index.t_evals)
            .zip(&s_1_evals)
            .zip(&s_2_evals)
            .take(f_evals.len() - 1)
            .map(|((((i, f), t), s_1), s_2)| {
                let one_plus_delta = F::one() + state.index.delta;
                let epsilon_one_plus_delta = state.index.epsilon * one_plus_delta;
                one_plus_delta
                    * (state.index.epsilon + f)
                    * (epsilon_one_plus_delta + t + state.index.delta * state.index.t_evals[i + 1])
                    * ((epsilon_one_plus_delta + s_1 + *s_2 * state.index.delta)
                        * (epsilon_one_plus_delta + s_2 + state.index.delta * s_1_evals[i + 1]))
                        .inverse()
                        .unwrap()
            })
            .collect::<Vec<F>>();

        // Create evaluations for z_2
        // First element is one
        let mut l_1 = F::one();
        let mut z_2_evals = Vec::with_capacity(constraint_domain.size());
        z_2_evals.push(l_1);
        for s in product_arguments {
            l_1 *= s;
            z_2_evals.push(l_1);
        }

        let z_2 = Self::calculate_opening_and_commitment_polys(label_z_2, &z_2_evals, will_be_evaluated, state, r);

        PoolResult::TablePolys(vec![
            (f.0, f.1, f_evals),
            (s_1.0, s_1.1, s_1_evals),
            (s_2.0, s_2.1, s_2_evals),
            (z_2.0, z_2.1, z_2_evals),
        ])
    }
}

#[derive(Debug)]
pub enum PoolResult<'a, F: PrimeField> {
    Witness(LabeledPolynomial<F>),
    MatrixPoly(LabeledPolynomial<F>, LabeledPolynomialWithBasis<'a, F>),
    TablePolys(Vec<(LabeledPolynomial<F>, LabeledPolynomialWithBasis<'a, F>, Vec<F>)>),
}

impl<'a, F: PrimeField> PoolResult<'a, F> {
    fn witness(self) -> Option<LabeledPolynomial<F>> {
        match self {
            Self::Witness(poly) => Some(poly),
            _ => None,
        }
    }

    fn z_m(self) -> Option<(LabeledPolynomial<F>, LabeledPolynomialWithBasis<'a, F>)> {
        match self {
            Self::MatrixPoly(p1, p2) => Some((p1, p2)),
            _ => None,
        }
    }

    fn table_polys(self) -> Option<Vec<(LabeledPolynomial<F>, LabeledPolynomialWithBasis<'a, F>, Vec<F>)>> {
        match self {
            Self::TablePolys(polys) => Some(polys),
            _ => None,
        }
    }
}
