// Copyright (C) 2019-2021 Aleo Systems Inc.
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
    polycommit::{LabeledPolynomial, LabeledPolynomialWithBasis, PolynomialWithBasis},
    snark::marlin::{
        ahp::{
            indexer::{Circuit, CircuitInfo, Matrix},
            prover::ProverConstraintSystem,
            verifier::{VerifierFirstMessage, VerifierSecondMessage},
            AHPError,
            AHPForR1CS,
            UnnormalizedBivariateLagrangePoly,
        },
        matrices::MatrixArithmetization,
        prover::{state::ProverState, ProverMessage},
        verifier::VerifierThirdMessage,
        MarlinMode,
    },
};
use snarkvm_fields::{batch_inversion_and_mul, PrimeField};
use snarkvm_r1cs::ConstraintSynthesizer;
use snarkvm_utilities::{cfg_into_iter, cfg_iter, cfg_iter_mut};

use itertools::Itertools;
use rand_core::RngCore;

#[cfg(not(feature = "std"))]
use snarkvm_utilities::println;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// The first set of prover oracles.
#[derive(Debug, Clone)]
pub struct ProverFirstOracles<'a, F: PrimeField> {
    /// The evaluations of `Az`.
    pub z_a: LabeledPolynomialWithBasis<'a, F>,
    /// The evaluations of `Bz`.
    pub z_b: LabeledPolynomialWithBasis<'a, F>,
    /// The sum-check hiding polynomial.
    pub mask_poly: Option<LabeledPolynomial<F>>,
    /// The LDE of `w`.
    pub w_poly: LabeledPolynomial<F>,
    /// The LDE of `Az`.
    pub z_a_poly: LabeledPolynomial<F>,
    /// The LDE of `Bz`.
    pub z_b_poly: LabeledPolynomial<F>,
}

impl<'a, F: PrimeField> ProverFirstOracles<'a, F> {
    /// Iterate over the polynomials output by the prover in the first round.
    /// Intended for use when committing.
    pub fn iter_for_commit(&'a self) -> impl Iterator<Item = LabeledPolynomialWithBasis<'a, F>> {
        [
            Some(&self.w_poly).map(Into::into),
            Some(self.z_a.clone()),
            Some(self.z_b.clone()),
            self.mask_poly.as_ref().map(Into::into),
        ]
        .into_iter()
        .flatten()
    }

    /// Iterate over the polynomials output by the prover in the first round.
    /// Intended for use when opening.
    pub fn iter_for_open(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        [Some(&self.w_poly), Some(&self.z_a_poly), Some(&self.z_b_poly), self.mask_poly.as_ref()].into_iter().flatten()
    }
}

/// The second set of prover oracles.
#[derive(Debug)]
pub struct ProverSecondOracles<F: PrimeField> {
    /// The polynomial `g` resulting from the first sumcheck.
    pub g_1: LabeledPolynomial<F>,
    /// The polynomial `h` resulting from the first sumcheck.
    pub h_1: LabeledPolynomial<F>,
}

impl<F: PrimeField> ProverSecondOracles<F> {
    /// Iterate over the polynomials output by the prover in the second round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        [&self.g_1, &self.h_1].into_iter()
    }
}

/// The third set of prover oracles.
#[derive(Debug)]
pub struct ProverThirdOracles<F: PrimeField> {
    /// The polynomial `g_a` resulting from the second sumcheck.
    pub g_a: LabeledPolynomial<F>,
    /// The polynomial `g_b` resulting from the second sumcheck.
    pub g_b: LabeledPolynomial<F>,
    /// The polynomial `g_c` resulting from the second sumcheck.
    pub g_c: LabeledPolynomial<F>,
}

impl<F: PrimeField> ProverThirdOracles<F> {
    /// Iterate over the polynomials output by the prover in the third round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        [&self.g_a, &self.g_b, &self.g_c].into_iter()
    }
}

#[derive(Debug)]
pub struct ProverFourthOracles<F: PrimeField> {
    /// The polynomial `h_2` resulting from the second sumcheck.
    pub h_2: LabeledPolynomial<F>,
}

impl<F: PrimeField> ProverFourthOracles<F> {
    /// Iterate over the polynomials output by the prover in the third round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        [&self.h_2].into_iter()
    }
}

impl<F: PrimeField, MM: MarlinMode> AHPForR1CS<F, MM> {
    /// Initialize the AHP prover.
    pub fn prover_init<'a, C: ConstraintSynthesizer<F>>(
        index: &'a Circuit<F, MM>,
        circuit: &C,
    ) -> Result<ProverState<'a, F, MM>, AHPError> {
        let init_time = start_timer!(|| "AHP::Prover::Init");

        let constraint_time = start_timer!(|| "Generating constraints and witnesses");
        let mut pcs = ProverConstraintSystem::new();
        circuit.generate_constraints(&mut pcs)?;
        end_timer!(constraint_time);

        let padding_time = start_timer!(|| "Padding matrices to make them square");
        crate::snark::marlin::ahp::matrices::pad_input_for_indexer_and_prover(&mut pcs);
        pcs.make_matrices_square();
        end_timer!(padding_time);

        let num_non_zero_a = index.index_info.num_non_zero_a;
        let num_non_zero_b = index.index_info.num_non_zero_b;
        let num_non_zero_c = index.index_info.num_non_zero_c;

        let ProverConstraintSystem {
            public_variables: padded_public_variables,
            private_variables,
            num_constraints,
            num_public_variables,
            num_private_variables,
            ..
        } = pcs;

        assert_eq!(padded_public_variables.len(), num_public_variables);
        assert!(padded_public_variables[0].is_one());
        assert_eq!(private_variables.len(), num_private_variables);

        if cfg!(debug_assertions) {
            println!("Number of padded public variables in Prover::Init: {}", num_public_variables);
            println!("Number of private variables: {}", num_private_variables);
            println!("Number of constraints: {}", num_constraints);
            println!("Number of non-zero entries in A: {}", num_non_zero_a);
            println!("Number of non-zero entries in B: {}", num_non_zero_b);
            println!("Number of non-zero entries in C: {}", num_non_zero_c);
        }

        if index.index_info.num_constraints != num_constraints
            || index.index_info.num_variables != (num_public_variables + num_private_variables)
        {
            return Err(AHPError::InstanceDoesNotMatchIndex);
        }

        if !Self::formatted_public_input_is_admissible(&padded_public_variables) {
            return Err(AHPError::InvalidPublicInputLength);
        }

        // Perform matrix multiplications.
        let inner_product = |row: &[(F, usize)]| {
            let mut result = F::zero();

            for &(ref coefficient, i) in row {
                // Fetch the variable.
                let variable = match i < num_public_variables {
                    true => padded_public_variables[i],
                    false => private_variables[i - num_public_variables],
                };

                result += &(if coefficient.is_one() { variable } else { variable * coefficient });
            }

            result
        };

        let eval_z_a_time = start_timer!(|| "Evaluating z_A");
        let z_a = index.a.iter().map(|row| inner_product(row)).collect();
        end_timer!(eval_z_a_time);

        let eval_z_b_time = start_timer!(|| "Evaluating z_B");
        let z_b = index.b.iter().map(|row| inner_product(row)).collect();
        end_timer!(eval_z_b_time);

        let zk_bound = 1; // One query is sufficient for our desired soundness

        end_timer!(init_time);
        let mut state = ProverState::initialize(padded_public_variables, private_variables, zk_bound, index)?;
        state.z_a = Some(z_a);
        state.z_b = Some(z_b);

        Ok(state)
    }

    /// Output the first round message and the next state.
    #[allow(clippy::type_complexity)]
    pub fn prover_first_round<'a, R: RngCore>(
        mut state: ProverState<'a, F, MM>,
        rng: &mut R,
    ) -> Result<(ProverMessage<F>, ProverFirstOracles<'a, F>, ProverState<'a, F, MM>), AHPError> {
        let round_time = start_timer!(|| "AHP::Prover::FirstRound");
        let constraint_domain = state.constraint_domain;
        let zk_bound = state.zk_bound;

        let v_H = constraint_domain.vanishing_polynomial();

        let x_time = start_timer!(|| "Computing x polynomial and evals");
        let input_domain = state.input_domain;
        let x_poly =
            EvaluationsOnDomain::from_vec_and_domain(state.padded_public_variables.clone(), input_domain).interpolate();
        let x_evals = constraint_domain.fft(&x_poly);
        end_timer!(x_time);

        let ratio = constraint_domain.size() / input_domain.size();

        let mut w_extended = state.private_variables.clone();
        w_extended.extend(
            core::iter::repeat(F::zero())
                .take(constraint_domain.size() - input_domain.size() - state.private_variables.len()),
        );

        let w_poly_time = start_timer!(|| "Computing w polynomial");
        let w_poly_evals = cfg_into_iter!(0..constraint_domain.size())
            .map(|k| if k % ratio == 0 { F::zero() } else { w_extended[k - (k / ratio) - 1] - x_evals[k] })
            .collect();

        let z_a_evals = EvaluationsOnDomain::from_vec_and_domain(state.z_a.unwrap(), constraint_domain);
        let z_b_evals = EvaluationsOnDomain::from_vec_and_domain(state.z_b.unwrap(), constraint_domain);
        state.z_a = None;
        state.z_b = None;

        let mut job_pool = snarkvm_utilities::ExecutionPool::with_capacity(3);
        let w_rand = F::rand(rng);
        job_pool.add_job(|| {
            let mut w_poly = EvaluationsOnDomain::from_vec_and_domain(w_poly_evals, constraint_domain).interpolate();
            if MM::ZK {
                w_poly += &(&v_H * w_rand);
            }
            let (w_poly, remainder) = w_poly.divide_by_vanishing_poly(input_domain).unwrap();
            assert!(remainder.is_zero());
            w_poly
        });

        end_timer!(w_poly_time);

        let r_a = F::rand(rng);
        job_pool.add_job(|| {
            let z_a_poly_time = start_timer!(|| "Computing z_A polynomial");
            let mut z_a_poly = z_a_evals.interpolate_by_ref();
            if MM::ZK {
                z_a_poly += &(&v_H * r_a);
            }
            end_timer!(z_a_poly_time);
            z_a_poly
        });

        let r_b = F::rand(rng);
        job_pool.add_job(|| {
            let z_b_poly_time = start_timer!(|| "Computing z_B polynomial");
            let mut z_b_poly = z_b_evals.interpolate_by_ref();
            if MM::ZK {
                z_b_poly += &(&v_H * r_b);
            }
            end_timer!(z_b_poly_time);
            z_b_poly
        });
        let [w_poly, z_a_poly, z_b_poly]: [DensePolynomial<F>; 3] = job_pool.execute_all().try_into().unwrap();

        let mask_poly = if MM::ZK {
            let mask_poly_time = start_timer!(|| "Computing mask polynomial");
            // We'll use the masking technique from Lunar (https://eprint.iacr.org/2020/1069.pdf, pgs 20-22).
            let h_1_mask = DensePolynomial::rand(3, rng).coeffs; // selected arbitrarily.
            let h_1_mask = SparsePolynomial::from_coefficients_vec(h_1_mask.into_iter().enumerate().collect())
                .mul(&constraint_domain.vanishing_polynomial());
            assert_eq!(h_1_mask.degree(), constraint_domain.size() + 3);
            // multiply g_1_mask by X
            let mut g_1_mask = DensePolynomial::rand(5, rng);
            g_1_mask.coeffs[0] = F::zero();
            let g_1_mask = SparsePolynomial::from_coefficients_vec(
                g_1_mask.iter().enumerate().filter_map(|(i, coeff)| (!coeff.is_zero()).then(|| (i, *coeff))).collect(),
            );

            let mut mask_poly = h_1_mask;
            mask_poly += &g_1_mask;
            end_timer!(mask_poly_time);
            debug_assert!(constraint_domain.elements().map(|z| mask_poly.evaluate(z)).sum::<F>().is_zero());
            assert_eq!(mask_poly.degree(), constraint_domain.size() + 3);
            assert!(mask_poly.degree() <= 3 * constraint_domain.size() + 2 * zk_bound - 3);
            Some(mask_poly)
        } else {
            None
        };

        let msg = ProverMessage::default();

        let hiding_bound = if MM::ZK { Some(1) } else { None };

        let w_poly = LabeledPolynomial::new("w".to_string(), w_poly, None, hiding_bound);
        let z_a_poly = LabeledPolynomial::new("z_a".to_string(), z_a_poly, None, hiding_bound);
        let z_b_poly = LabeledPolynomial::new("z_b".to_string(), z_b_poly, None, hiding_bound);

        assert!(w_poly.degree() < constraint_domain.size() - input_domain.size() + zk_bound);
        assert!(z_a_poly.degree() < constraint_domain.size() + zk_bound);
        assert!(z_b_poly.degree() < constraint_domain.size() + zk_bound);

        let mask_poly =
            mask_poly.map(|mask_poly| LabeledPolynomial::new("mask_poly".to_string(), mask_poly, None, None));

        let z_a_evals = PolynomialWithBasis::new_lagrange_basis(z_a_evals);
        let mut z_a = vec![(F::one(), z_a_evals)];
        if MM::ZK {
            let r_a_v_H = PolynomialWithBasis::new_sparse_monomial_basis(&v_H * r_a, None);
            z_a.push((F::one(), r_a_v_H));
        }
        let z_a = LabeledPolynomialWithBasis::new_linear_combination("z_a".to_string(), z_a, hiding_bound);

        let z_b_evals = PolynomialWithBasis::new_lagrange_basis(z_b_evals);
        let mut z_b = vec![(F::one(), z_b_evals)];
        if MM::ZK {
            let r_b_v_H = PolynomialWithBasis::new_sparse_monomial_basis(&v_H * r_b, None);
            z_b.push((F::one(), r_b_v_H));
        }
        let z_b = LabeledPolynomialWithBasis::new_linear_combination("z_b".to_string(), z_b, hiding_bound);

        let oracles = ProverFirstOracles { z_a, z_b, mask_poly: mask_poly.clone(), z_a_poly, z_b_poly, w_poly };

        state.w_poly = Some(oracles.w_poly.clone());
        state.mz_polys = Some((oracles.z_a_poly.clone(), oracles.z_b_poly.clone()));
        state.mz_poly_randomizer = Some((r_a, r_b));
        state.mask_poly = mask_poly;
        end_timer!(round_time);

        Ok((msg, oracles, state))
    }

    fn calculate_t<'a>(
        matrices: &[&'a Matrix<F>],
        matrix_randomizers: [F; 3],
        input_domain: EvaluationDomain<F>,
        constraint_domain: EvaluationDomain<F>,
        r_alpha_x_on_h: &[F],
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
        EvaluationsOnDomain::from_vec_and_domain(t_evals_on_h, constraint_domain).interpolate()
    }

    /// Output the number of oracles sent by the prover in the first round.
    pub fn prover_num_first_round_oracles() -> usize {
        if MM::ZK { 4 } else { 3 }
    }

    /// Output the degree bounds of oracles in the first round.
    pub fn prover_first_round_degree_bounds(_info: &CircuitInfo<F>) -> impl Iterator<Item = Option<usize>> {
        if MM::ZK { core::iter::repeat(None).take(4) } else { core::iter::repeat(None).take(3) }
    }

    /// Output the second round message and the next state.
    pub fn prover_second_round<'a, R: RngCore>(
        verifier_message: &VerifierFirstMessage<F>,
        mut state: ProverState<'a, F, MM>,
        _r: &mut R,
    ) -> (ProverMessage<F>, ProverSecondOracles<F>, ProverState<'a, F, MM>) {
        let round_time = start_timer!(|| "AHP::Prover::SecondRound");

        let constraint_domain = state.constraint_domain;
        let zk_bound = state.zk_bound;

        let mask_poly = state.mask_poly.as_ref();
        assert_eq!(MM::ZK, mask_poly.is_some());

        let VerifierFirstMessage { alpha, eta_b, eta_c } = *verifier_message;

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
            let mut z_c = &z_a_poly_det * &z_b_poly_det;
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
            z_a_poly * z_b_poly
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
            );
            end_timer!(t_poly_time);
            t_poly
        });
        let [summed_z_m, t_poly]: [DensePolynomial<F>; 2] = job_pool.execute_all().try_into().unwrap();

        let z_poly_time = start_timer!(|| "Compute z poly");

        let x_poly =
            EvaluationsOnDomain::from_vec_and_domain(state.padded_public_variables.clone(), state.input_domain)
                .interpolate();
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
        let mut job_pool = snarkvm_utilities::ExecutionPool::with_capacity(4);
        job_pool.add_job(|| {
            let r_alpha_x_evals = constraint_domain
                .batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs_over_domain(alpha, &mul_domain);
            EvaluationsOnDomain::from_vec_and_domain(r_alpha_x_evals, mul_domain)
        });
        job_pool.add_job(|| summed_z_m.evaluate_over_domain_by_ref(mul_domain));
        job_pool.add_job(|| z_poly.evaluate_over_domain_by_ref(mul_domain));
        job_pool.add_job(|| t_poly.evaluate_over_domain_by_ref(mul_domain));
        let [mut r_alpha_evals, summed_z_m_evals, z_poly_evals, t_poly_m_evals]: [_; 4] =
            job_pool.execute_all().try_into().unwrap();

        cfg_iter_mut!(r_alpha_evals.evaluations)
            .zip(&summed_z_m_evals.evaluations)
            .zip(&z_poly_evals.evaluations)
            .zip(&t_poly_m_evals.evaluations)
            .for_each(|(((a, b), &c), d)| {
                *a *= b;
                *a -= &(c * d);
            });
        let mut rhs = r_alpha_evals.interpolate();
        rhs += mask_poly.map_or(&SparsePolynomial::zero(), |p| p.polynomial().as_sparse().unwrap());
        let q_1 = rhs;
        end_timer!(q_1_time);

        let sumcheck_time = start_timer!(|| "Compute sumcheck h and g polys");
        let (h_1, x_g_1) = q_1.divide_by_vanishing_poly(constraint_domain).unwrap();
        let g_1 = DensePolynomial::from_coefficients_slice(&x_g_1.coeffs[1..]);
        end_timer!(sumcheck_time);

        let msg = ProverMessage::default();

        assert!(g_1.degree() <= constraint_domain.size() - 2);
        assert!(h_1.degree() <= 2 * constraint_domain.size() + 2 * zk_bound - 2);

        let hiding_bound = if MM::ZK { Some(1) } else { None };
        let oracles = ProverSecondOracles {
            g_1: LabeledPolynomial::new("g_1".into(), g_1, Some(constraint_domain.size() - 2), hiding_bound),
            h_1: LabeledPolynomial::new("h_1".into(), h_1, None, None),
        };

        state.w_poly = None;
        state.verifier_first_message = Some(*verifier_message);
        end_timer!(round_time);

        (msg, oracles, state)
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

    /// Output the third round message and the next state.
    pub fn prover_third_round<'a, R: RngCore>(
        verifier_message: &VerifierSecondMessage<F>,
        mut state: ProverState<'a, F, MM>,
        _r: &mut R,
    ) -> Result<(ProverMessage<F>, ProverThirdOracles<F>, ProverState<'a, F, MM>), AHPError> {
        let round_time = start_timer!(|| "AHP::Prover::ThirdRound");

        let VerifierFirstMessage { alpha, .. } = state
            .verifier_first_message
            .expect("ProverState should include verifier_first_msg when prover_third_round is called");

        let beta = verifier_message.beta;

        let v_H_at_alpha = state.constraint_domain.evaluate_vanishing_polynomial(alpha);
        let v_H_at_beta = state.constraint_domain.evaluate_vanishing_polynomial(beta);

        let v_H_alpha_v_H_beta = v_H_at_alpha * v_H_at_beta;

        let largest_non_zero_domain_size = Self::max_non_zero_domain(&state.index.index_info).size_as_field_element;
        let (sum_a, lhs_a, g_a) = Self::third_round_helper(
            "a",
            state.non_zero_a_domain,
            &state.index.a_arith,
            alpha,
            beta,
            v_H_alpha_v_H_beta,
            largest_non_zero_domain_size,
        );
        let (sum_b, lhs_b, g_b) = Self::third_round_helper(
            "b",
            state.non_zero_b_domain,
            &state.index.b_arith,
            alpha,
            beta,
            v_H_alpha_v_H_beta,
            largest_non_zero_domain_size,
        );
        let (sum_c, lhs_c, g_c) = Self::third_round_helper(
            "c",
            state.non_zero_c_domain,
            &state.index.c_arith,
            alpha,
            beta,
            v_H_alpha_v_H_beta,
            largest_non_zero_domain_size,
        );

        let msg = ProverMessage { field_elements: vec![sum_a, sum_b, sum_c] };
        let oracles = ProverThirdOracles { g_a, g_b, g_c };
        state.lhs_polynomials = Some([lhs_a, lhs_b, lhs_c]);
        state.sums = Some([sum_a, sum_b, sum_c]);

        end_timer!(round_time);

        Ok((msg, oracles, state))
    }

    fn third_round_helper(
        label: &str,
        non_zero_domain: EvaluationDomain<F>,
        arithmetization: &MatrixArithmetization<F>,
        alpha: F,
        beta: F,
        v_H_alpha_v_H_beta: F,
        largest_non_zero_domain_size: F,
    ) -> (F, DensePolynomial<F>, LabeledPolynomial<F>) {
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
                EvaluationsOnDomain::from_vec_and_domain(evals, non_zero_domain).interpolate()
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
        let f = EvaluationsOnDomain::from_vec_and_domain(f_evals_on_K, non_zero_domain).interpolate();
        end_timer!(f_poly_time);
        let g = DensePolynomial::from_coefficients_slice(&f.coeffs[1..]);
        let mut h = &a_poly - &(&b_poly * &f);
        // Let K_max = largest_non_zero_domain;
        // Let K = non_zero_domain;
        // Let s := K_max.selector_polynomial(K);
        // Let v_K_max := K_max.vanishing_polynomial();
        // Let v_K := K.vanishing_polynomial();

        // Later on, we multiply `h` by s, and divide by v_K_max.
        // However, s := (v_K_max / v_K) * (v_K.size() / v_K_max.size());
        // Therefore, h * s / v_K_max = h / v_K * (v_K.size() / v_K_max.size());
        // That's what we're computing here.
        let result = h.divide_by_vanishing_poly(non_zero_domain).unwrap();
        assert!(result.1.is_zero());
        h = result.0;
        let multiplier = non_zero_domain.size_as_field_element / largest_non_zero_domain_size;
        cfg_iter_mut!(h.coeffs).for_each(|c| *c *= multiplier);

        let g = LabeledPolynomial::new("g_".to_string() + label, g, Some(non_zero_domain.size() - 2), None);

        assert!(h.degree() <= non_zero_domain.size() - 2);
        assert!(g.degree() <= non_zero_domain.size() - 2);
        (f.coeffs[0], h, g)
    }

    /// Output the number of oracles sent by the prover in the third round.
    pub fn prover_num_third_round_oracles() -> usize {
        3
    }

    /// Output the degree bounds of oracles in the third round.
    pub fn prover_third_round_degree_bounds(info: &CircuitInfo<F>) -> impl Iterator<Item = Option<usize>> {
        let non_zero_a_size = EvaluationDomain::<F>::compute_size_of_domain(info.num_non_zero_a).unwrap();
        let non_zero_b_size = EvaluationDomain::<F>::compute_size_of_domain(info.num_non_zero_b).unwrap();
        let non_zero_c_size = EvaluationDomain::<F>::compute_size_of_domain(info.num_non_zero_c).unwrap();

        [Some(non_zero_a_size - 2), Some(non_zero_b_size - 2), Some(non_zero_c_size - 2)].into_iter()
    }

    /// Output the fourth round message and the next state.
    pub fn prover_fourth_round<'a, R: RngCore>(
        verifier_message: &VerifierThirdMessage<F>,
        state: ProverState<'a, F, MM>,
        _r: &mut R,
    ) -> Result<(ProverMessage<F>, ProverFourthOracles<F>), AHPError> {
        let VerifierThirdMessage { r_b, r_c, .. } = verifier_message;
        let [mut lhs_a, lhs_b, lhs_c] = state.lhs_polynomials.unwrap();
        lhs_a += &(&(lhs_b * *r_b) + &(lhs_c * *r_c));
        let msg = ProverMessage::default();
        let h_2 = LabeledPolynomial::new("h_2".into(), lhs_a, None, None);
        let oracles = ProverFourthOracles { h_2 };
        Ok((msg, oracles))
    }

    /// Output the number of oracles sent by the prover in the third round.
    pub fn prover_num_fourth_round_oracles() -> usize {
        1
    }

    /// Output the degree bounds of oracles in the third round.
    pub fn prover_fourth_round_degree_bounds(_: &CircuitInfo<F>) -> impl Iterator<Item = Option<usize>> {
        [None].into_iter()
    }
}

#[test]
fn check_division_by_vanishing_poly_preserve_sparseness() {
    use snarkvm_curves::bls12_377::Fr;
    use snarkvm_fields::{Field, One, Zero};
    let domain = EvaluationDomain::new(16).unwrap();
    let small_domain = EvaluationDomain::new(4).unwrap();
    let val = Fr::one().double().double().double() - Fr::one();
    let mut evals = (0..16).map(|pow| val.pow([pow])).collect::<Vec<_>>();
    for i in 0..4 {
        evals[4 * i] = Fr::zero();
    }
    let p = EvaluationsOnDomain::from_vec_and_domain(evals, domain).interpolate();
    let (p_div_v, p_mod_v) = p.divide_by_vanishing_poly(small_domain).unwrap();
    assert!(p_mod_v.is_zero());
    dbg!(p_div_v.evaluate_over_domain(domain));
}
