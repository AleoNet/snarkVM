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

use crate::{
    fft::{DensePolynomial, EvaluationDomain, Evaluations as EvaluationsOnDomain, SparsePolynomial},
    polycommit::sonic_pc::{LabeledPolynomial, LabeledPolynomialWithBasis, PolynomialWithBasis},
    snark::marlin::{
        ahp::{indexer::CircuitInfo, AHPError, AHPForR1CS},
        prover,
        MarlinMode,
    },
};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::cfg_into_iter;

use rand_core::RngCore;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

impl<F: PrimeField, MM: MarlinMode> AHPForR1CS<F, MM> {
    /// Output the number of oracles sent by the prover in the first round.
    pub fn prover_num_first_round_oracles() -> usize {
        if MM::ZK { 4 } else { 3 }
    }

    /// Output the degree bounds of oracles in the first round.
    pub fn prover_first_round_degree_bounds(_info: &CircuitInfo<F>) -> impl Iterator<Item = Option<usize>> {
        if MM::ZK { core::iter::repeat(None).take(4) } else { core::iter::repeat(None).take(3) }
    }

    /// Output the first round message and the next state.
    #[allow(clippy::type_complexity)]
    pub fn prover_first_round<'a, R: RngCore>(
        mut state: prover::State<'a, F, MM>,
        rng: &mut R,
    ) -> Result<(prover::FirstOracles<'a, F>, prover::State<'a, F, MM>), AHPError> {
        let round_time = start_timer!(|| "AHP::Prover::FirstRound");
        let constraint_domain = state.constraint_domain;
        let zk_bound = state.zk_bound;

        let mut job_pool = snarkvm_utilities::ExecutionPool::with_capacity(3);
        let z_a = state.z_a.take().unwrap();
        let z_b = state.z_b.take().unwrap();
        let private_variables = core::mem::take(&mut state.private_variables);
        job_pool.add_job(|| Self::calculate_w(private_variables, &state));

        job_pool.add_job(|| Self::calculate_z_m("z_a", z_a, false, &state, None));

        let r_b = Some(F::rand(rng));
        job_pool.add_job(|| Self::calculate_z_m("z_b", z_b, true, &state, r_b));
        let [w, z_a, z_b]: [PoolResult<F>; 3] = job_pool.execute_all().try_into().unwrap();
        let w_poly = w.witness().unwrap();
        let (z_a_poly, z_a) = z_a.z_m().unwrap();
        let (z_b_poly, z_b) = z_b.z_m().unwrap();

        let mask_poly = Self::calculate_mask_poly(constraint_domain, zk_bound, rng);

        let oracles = prover::FirstOracles { z_a, z_b, mask_poly: mask_poly.clone(), z_a_poly, z_b_poly, w_poly };

        state.w_poly = Some(oracles.w_poly.clone());
        state.mz_polys = Some((oracles.z_a_poly.clone(), oracles.z_b_poly.clone()));
        state.mz_poly_randomizer = r_b;
        state.mask_poly = mask_poly;
        end_timer!(round_time);

        Ok((oracles, state))
    }

    fn calculate_mask_poly<R: RngCore>(
        constraint_domain: EvaluationDomain<F>,
        zk_bound: Option<usize>,
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
                assert!(mask_poly.degree() <= 3 * constraint_domain.size() + 2 * zk_bound.unwrap() - 3);

                end_timer!(mask_poly_time);
                mask_poly
            })
            .map(|mask_poly| LabeledPolynomial::new("mask_poly".to_string(), mask_poly, None, None))
    }

    fn calculate_w<'a>(private_variables: Vec<F>, state: &prover::State<'a, F, MM>) -> PoolResult<'a, F> {
        let constraint_domain = state.constraint_domain;
        let input_domain = state.input_domain;

        let mut w_extended = private_variables;
        let ratio = constraint_domain.size() / input_domain.size();
        w_extended.resize(constraint_domain.size() - input_domain.size(), F::zero());

        let x_evals = {
            let mut coeffs = state.x_poly.coeffs.clone();
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
        PoolResult::Witness(LabeledPolynomial::new("w".to_string(), w_poly, None, state.zk_bound))
    }

    fn calculate_z_m<'a>(
        label: impl ToString,
        evaluations: Vec<F>,
        will_be_evaluated: bool,
        state: &prover::State<'a, F, MM>,
        r: Option<F>,
    ) -> PoolResult<'a, F> {
        let constraint_domain = state.constraint_domain;
        let v_H = constraint_domain.vanishing_polynomial();
        let should_randomize = MM::ZK && will_be_evaluated;
        let label = label.to_string();
        let poly_time = start_timer!(|| format!("Computing {label}"));

        let evals = EvaluationsOnDomain::from_vec_and_domain(evaluations, constraint_domain);

        let mut poly = evals.interpolate_with_pc_by_ref(state.ifft_precomputation());
        if should_randomize {
            poly += &(&v_H * r.unwrap());
        }

        let hiding_bound = if MM::ZK { Some(1) } else { None };

        let poly_for_opening = LabeledPolynomial::new(label.to_string(), poly, None, hiding_bound);
        if should_randomize {
            assert!(poly_for_opening.degree() < constraint_domain.size() + hiding_bound.unwrap());
        } else {
            assert!(poly_for_opening.degree() < constraint_domain.size());
        }

        let poly_for_committing = if should_randomize {
            let poly_terms = vec![
                (F::one(), PolynomialWithBasis::new_lagrange_basis(evals)),
                (F::one(), PolynomialWithBasis::new_sparse_monomial_basis(&v_H * r.unwrap(), None)),
            ];
            LabeledPolynomialWithBasis::new_linear_combination(label, poly_terms, hiding_bound)
        } else {
            LabeledPolynomialWithBasis::new_lagrange_basis(label, evals, hiding_bound)
        };
        end_timer!(poly_time);

        PoolResult::MatrixPoly(poly_for_opening, poly_for_committing)
    }
}

#[derive(Debug)]
pub enum PoolResult<'a, F: PrimeField> {
    Witness(LabeledPolynomial<F>),
    MatrixPoly(LabeledPolynomial<F>, LabeledPolynomialWithBasis<'a, F>),
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
}
