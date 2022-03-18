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
    fft::{
        domain::IFFTPrecomputation,
        polynomial::PolyMultiplier,
        DensePolynomial,
        EvaluationDomain,
        Evaluations as EvaluationsOnDomain,
        SparsePolynomial,
    },
    polycommit::LabeledPolynomial,
    snark::marlin::{
        ahp::{
            indexer::{CircuitInfo, Matrix},
            verifier,
            AHPForR1CS,
            UnnormalizedBivariateLagrangePoly,
        },
        prover,
        MarlinMode,
    },
};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::cfg_iter_mut;

use itertools::Itertools;
use rand_core::RngCore;

#[cfg(not(feature = "std"))]
use snarkvm_utilities::println;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

impl<F: PrimeField, MM: MarlinMode> AHPForR1CS<F, MM> {
    /// Output the second round message and the next state.
    pub fn prover_second_round<'a, R: RngCore>(
        verifier_message: &verifier::FirstMessage<F>,
        mut state: prover::State<'a, F, MM>,
        _r: &mut R,
    ) -> (prover::SecondOracles<F>, prover::State<'a, F, MM>) {
        let round_time = start_timer!(|| "AHP::Prover::SecondRound");

        let constraint_domain = state.constraint_domain;
        let zk_bound = state.zk_bound;

        let mask_poly = state.mask_poly.as_ref();
        assert_eq!(MM::ZK, mask_poly.is_some());

        let verifier::FirstMessage { alpha, eta_b, eta_c } = *verifier_message;

        let summed_z_m_poly_time = start_timer!(|| "Compute z_m poly");
        let (z_a_poly, z_b_poly) = state.mz_polys.as_ref().unwrap();
        if MM::ZK {
            assert_eq!(z_a_poly.degree(), constraint_domain.size());
            assert_eq!(z_b_poly.degree(), constraint_domain.size());
        } else {
            assert!(z_a_poly.degree() < constraint_domain.size());
            assert!(z_b_poly.degree() < constraint_domain.size());
        }
        let (z_a_poly, z_b_poly) = state.mz_polys.as_ref().unwrap();
        let (r_a, r_b) = state.mz_poly_randomizer.as_ref().unwrap();
        let z_a_poly = z_a_poly.polynomial().as_dense().unwrap();
        let z_b_poly = z_b_poly.polynomial().as_dense().unwrap();

        let z_c_poly = if MM::ZK {
            let v_H = constraint_domain.vanishing_polynomial();
            let r_a_v_H = v_H.mul(&SparsePolynomial::from_coefficients_slice(&[(0, *r_a)]));
            let r_b_v_H = v_H.mul(&SparsePolynomial::from_coefficients_slice(&[(0, *r_b)]));
            let z_a_poly_det = z_a_poly.clone() - &r_a_v_H;
            let z_b_poly_det = z_b_poly.clone() - &r_b_v_H;
            // z_c = (z_a + r_a * v_H) * (z_b + r_b * v_H);
            // z_c = z_a * z_b + r_a * z_b * v_H + r_b * z_a * v_H + r_a * r_b * v_H^2;
            let mut z_c = {
                let mut multiplier = PolyMultiplier::new();
                multiplier.add_polynomial_ref(&z_a_poly_det, "z_a_poly");
                multiplier.add_polynomial_ref(&z_b_poly_det, "z_b_poly");
                multiplier.add_precomputation(state.fft_precomputation(), state.ifft_precomputation());
                multiplier.multiply().unwrap()
            };
            z_c += &r_a_v_H.mul(&r_b_v_H);
            assert_eq!(z_c.degree(), 2 * constraint_domain.size());
            #[cfg(not(feature = "parallel"))]
            use core::iter::repeat;
            #[cfg(feature = "parallel")]
            use rayon::iter::repeat;

            // Zip safety: here `constraint_domain.size() + z_a_poly_det.coeffs.len()` could
            // have size smaller than `z_c.coeffs`, so `zip_eq` would be incorrect.
            let zero = F::zero();
            repeat(&zero)
                .take(constraint_domain.size())
                .chain(&z_a_poly_det.coeffs)
                .enumerate()
                .zip(&mut z_c.coeffs)
                .for_each(|((i, c), z_c)| {
                    let t = if i < constraint_domain.size() {
                        z_a_poly_det.coeffs.get(i).map_or(F::zero(), |c| -*c)
                    } else {
                        *c
                    };
                    *z_c += t * r_b;
                });

            // Zip safety: here `constraint_domain.size() + z_b_poly_det.coeffs.len()` could
            // have size smaller than `z_c.coeffs`, so `zip_eq` would be incorrect.
            repeat(&zero)
                .take(constraint_domain.size())
                .chain(&z_b_poly_det.coeffs)
                .enumerate()
                .zip(&mut z_c.coeffs)
                .for_each(|((i, c), z_c)| {
                    let t = if i < constraint_domain.size() {
                        z_b_poly_det.coeffs.get(i).map_or(F::zero(), |c| -*c)
                    } else {
                        *c
                    };
                    *z_c += t * r_a;
                });
            z_c
        } else {
            let mut multiplier = PolyMultiplier::new();
            multiplier.add_polynomial_ref(z_a_poly, "z_a_poly");
            multiplier.add_polynomial_ref(z_b_poly, "z_b_poly");
            multiplier.add_precomputation(state.fft_precomputation(), state.ifft_precomputation());
            multiplier.multiply().unwrap()
        };

        let mut job_pool = snarkvm_utilities::ExecutionPool::with_capacity(2);
        job_pool.add_job(|| {
            let mut summed_z_m_coeffs = z_c_poly.coeffs;
            // Note: Can't combine these two loops, because z_c_poly has 2x the degree
            // of z_a_poly and z_b_poly, so the second loop gets truncated due to
            // the `zip`s.
            cfg_iter_mut!(summed_z_m_coeffs).for_each(|c| *c *= &eta_c);
            cfg_iter_mut!(summed_z_m_coeffs)
                .zip(&z_a_poly.coeffs)
                .zip(&z_b_poly.coeffs)
                .for_each(|((c, a), b)| *c += eta_b * b + a);

            let summed_z_m = DensePolynomial::from_coefficients_vec(summed_z_m_coeffs);
            end_timer!(summed_z_m_poly_time);
            summed_z_m
        });
        job_pool.add_job(|| {
            let t_poly_time = start_timer!(|| "Compute t poly");

            let r_alpha_x_evals =
                constraint_domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(alpha);
            let t_poly = Self::calculate_t(
                &[&state.index.a, &state.index.b, &state.index.c],
                [F::one(), eta_b, eta_c],
                state.input_domain,
                state.constraint_domain,
                &r_alpha_x_evals,
                state.ifft_precomputation(),
            );
            end_timer!(t_poly_time);
            t_poly
        });
        let [summed_z_m, t_poly]: [DensePolynomial<F>; 2] = job_pool.execute_all().try_into().unwrap();

        let z_poly_time = start_timer!(|| "Compute z poly");

        let x_poly =
            EvaluationsOnDomain::from_vec_and_domain(state.padded_public_variables.clone(), state.input_domain)
                .interpolate_with_pc(state.ifft_precomputation());
        let w_poly = state.w_poly.as_ref().and_then(|p| p.polynomial().as_dense()).unwrap();
        let mut z_poly = w_poly.mul_by_vanishing_poly(state.input_domain);
        // Zip safety: `x_poly` is smaller than `z_poly`.
        cfg_iter_mut!(z_poly.coeffs).zip(&x_poly.coeffs).for_each(|(z, x)| *z += x);
        assert!(z_poly.degree() < constraint_domain.size() + zk_bound);

        end_timer!(z_poly_time);

        let q_1_time = start_timer!(|| "Compute q_1 poly");

        let mul_domain_size = *[
            mask_poly.map_or(0, |p| p.degree() + 1),
            constraint_domain.size() + summed_z_m.coeffs.len(),
            t_poly.coeffs.len() + z_poly.len(),
        ]
        .iter()
        .max()
        .unwrap();
        let mul_domain =
            EvaluationDomain::new(mul_domain_size).expect("field is not smooth enough to construct domain");
        let mut multiplier = PolyMultiplier::new();
        multiplier.add_precomputation(state.fft_precomputation(), state.ifft_precomputation());
        multiplier.add_polynomial(summed_z_m, "summed_z_m");
        multiplier.add_polynomial(z_poly, "z");
        multiplier.add_polynomial(t_poly, "t");
        let r_alpha_x_evals = {
            let r_alpha_x_evals = constraint_domain
                .batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs_over_domain(alpha, &mul_domain);
            EvaluationsOnDomain::from_vec_and_domain(r_alpha_x_evals, mul_domain)
        };
        multiplier.add_evaluation(r_alpha_x_evals, "r_alpha_x");
        let mut rhs = multiplier
            .element_wise_arithmetic_4_over_domain(mul_domain, ["r_alpha_x", "summed_z_m", "z", "t"], |a, b, c, d| {
                a * b - c * d
            })
            .unwrap();

        rhs += mask_poly.map_or(&SparsePolynomial::zero(), |p| p.polynomial().as_sparse().unwrap());
        let q_1 = rhs;
        end_timer!(q_1_time);

        let sumcheck_time = start_timer!(|| "Compute sumcheck h and g polys");
        let (h_1, x_g_1) = q_1.divide_by_vanishing_poly(constraint_domain).unwrap();
        let g_1 = DensePolynomial::from_coefficients_slice(&x_g_1.coeffs[1..]);
        drop(x_g_1);
        end_timer!(sumcheck_time);

        assert!(g_1.degree() <= constraint_domain.size() - 2);
        assert!(h_1.degree() <= 2 * constraint_domain.size() + 2 * zk_bound - 2);

        let hiding_bound = if MM::ZK { Some(1) } else { None };
        let oracles = prover::SecondOracles {
            g_1: LabeledPolynomial::new("g_1".into(), g_1, Some(constraint_domain.size() - 2), hiding_bound),
            h_1: LabeledPolynomial::new("h_1".into(), h_1, None, None),
        };

        state.w_poly = None;
        state.verifier_first_message = Some(*verifier_message);
        end_timer!(round_time);

        (oracles, state)
    }

    fn calculate_t<'a>(
        matrices: &[&'a Matrix<F>],
        matrix_randomizers: [F; 3],
        input_domain: EvaluationDomain<F>,
        constraint_domain: EvaluationDomain<F>,
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
        EvaluationsOnDomain::from_vec_and_domain(t_evals_on_h, constraint_domain)
            .interpolate_with_pc(ifft_precomputation)
    }

    /// Output the number of oracles sent by the prover in the second round.
    pub fn prover_num_second_round_oracles() -> usize {
        2
    }

    /// Output the degree bounds of oracles in the second round.
    pub fn prover_second_round_degree_bounds(info: &CircuitInfo<F>) -> impl Iterator<Item = Option<usize>> {
        let constraint_domain_size = EvaluationDomain::<F>::compute_size_of_domain(info.num_constraints).unwrap();

        [Some(constraint_domain_size - 2), None].into_iter()
    }
}
