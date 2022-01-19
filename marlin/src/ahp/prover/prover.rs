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
    ahp::{
        indexer::{Circuit, CircuitInfo, Matrix},
        prover::ProverConstraintSystem,
        verifier::{VerifierFirstMessage, VerifierSecondMessage},
        AHPError,
        AHPForR1CS,
        UnnormalizedBivariateLagrangePoly,
    },
    marlin::MarlinMode,
    prover::{state::ProverState, ProverMessage},
    ToString,
    Vec,
};
use snarkvm_algorithms::fft::{EvaluationDomain, Evaluations as EvaluationsOnDomain, SparsePolynomial};
use snarkvm_fields::{batch_inversion, Field, PrimeField};
use snarkvm_r1cs::errors::SynthesisError;
use snarkvm_utilities::{cfg_into_iter, cfg_iter, cfg_iter_mut};

use snarkvm_polycommit::{LabeledPolynomial, Polynomial};
use snarkvm_r1cs::ConstraintSynthesizer;

use rand_core::RngCore;

#[cfg(not(feature = "std"))]
use snarkvm_utilities::println;

#[cfg(feature = "parallel")]
use rayon::prelude::*;
use snarkvm_algorithms::fft::DensePolynomial;

/// The first set of prover oracles.
pub struct ProverFirstOracles<F: Field> {
    /// The LDE of `w`.
    pub w: LabeledPolynomial<F>,
    /// The LDE of `Az`.
    pub z_a: LabeledPolynomial<F>,
    /// The LDE of `Bz`.
    pub z_b: LabeledPolynomial<F>,
    /// The sum-check hiding polynomial.
    pub mask_poly: Option<LabeledPolynomial<F>>,
}

impl<F: Field> ProverFirstOracles<F> {
    /// Iterate over the polynomials output by the prover in the first round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        if let Some(mask_poly) = &self.mask_poly {
            vec![&self.w, &self.z_a, &self.z_b, mask_poly].into_iter()
        } else {
            vec![&self.w, &self.z_a, &self.z_b].into_iter()
        }
    }
}

/// The second set of prover oracles.
pub struct ProverSecondOracles<F: Field> {
    /// The polynomial `t` that is produced in the first round.
    pub t: LabeledPolynomial<F>,
    /// The polynomial `g` resulting from the first sumcheck.
    pub g_1: LabeledPolynomial<F>,
    /// The polynomial `h` resulting from the first sumcheck.
    pub h_1: LabeledPolynomial<F>,
}

impl<F: Field> ProverSecondOracles<F> {
    /// Iterate over the polynomials output by the prover in the second round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        vec![&self.t, &self.g_1, &self.h_1].into_iter()
    }
}

/// The third set of prover oracles.
pub struct ProverThirdOracles<F: Field> {
    /// The polynomial `g` resulting from the second sumcheck.
    pub g_2: LabeledPolynomial<F>,
    /// The polynomial `h` resulting from the second sumcheck.
    pub h_2: LabeledPolynomial<F>,
}

impl<F: Field> ProverThirdOracles<F> {
    /// Iterate over the polynomials output by the prover in the third round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        vec![&self.g_2, &self.h_2].into_iter()
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
        crate::ahp::matrices::pad_input_for_indexer_and_prover(&mut pcs);
        pcs.make_matrices_square();
        end_timer!(padding_time);

        let num_non_zero = index.index_info.num_non_zero;

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
            println!(
                "Number of padded public variables in Prover::Init: {}",
                num_public_variables
            );
            println!("Number of private variables: {}", num_private_variables);
            println!("Number of constraints: {}", num_constraints);
            println!("Number of num_non_zero: {}", num_non_zero);
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

                result += &(if coefficient.is_one() {
                    variable
                } else {
                    variable * coefficient
                });
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

        let domain_h = EvaluationDomain::new(num_constraints).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let domain_k = EvaluationDomain::new(num_non_zero).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let domain_x = EvaluationDomain::new(num_public_variables).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        end_timer!(init_time);

        Ok(ProverState {
            padded_public_variables,
            private_variables,
            z_a: Some(z_a),
            z_b: Some(z_b),
            w_poly: None,
            mz_polys: None,
            mz_poly_randomizer: None,
            zk_bound,
            index,
            verifier_first_message: None,
            mask_poly: None,
            domain_h,
            domain_k,
            domain_x,
        })
    }

    /// Output the first round message and the next state.
    #[allow(clippy::type_complexity)]
    pub fn prover_first_round<'a, R: RngCore>(
        mut state: ProverState<'a, F, MM>,
        rng: &mut R,
    ) -> Result<(ProverMessage<F>, ProverFirstOracles<F>, ProverState<'a, F, MM>), AHPError> {
        let round_time = start_timer!(|| "AHP::Prover::FirstRound");
        let domain_h = state.domain_h;
        let zk_bound = state.zk_bound;

        let v_H = domain_h.vanishing_polynomial();

        let x_time = start_timer!(|| "Computing x polynomial and evals");
        let domain_x = state.domain_x;
        let x_poly =
            EvaluationsOnDomain::from_vec_and_domain(state.padded_public_variables.clone(), domain_x).interpolate();
        let x_evals = domain_h.fft(&x_poly);
        end_timer!(x_time);

        let ratio = domain_h.size() / domain_x.size();

        let mut w_extended = state.private_variables.clone();
        w_extended.extend(vec![
            F::zero();
            domain_h.size() - domain_x.size() - state.private_variables.len()
        ]);

        let w_poly_time = start_timer!(|| "Computing w polynomial");
        let w_poly_evals = cfg_into_iter!(0..domain_h.size())
            .map(|k| {
                if k % ratio == 0 {
                    F::zero()
                } else {
                    w_extended[k - (k / ratio) - 1] - x_evals[k]
                }
            })
            .collect();

        let mut job_pool = snarkvm_utilities::ExecutionPool::with_capacity(3);
        let w_rand = F::rand(rng);
        job_pool.add_job(|| {
            let w_poly = &EvaluationsOnDomain::from_vec_and_domain(w_poly_evals, domain_h).interpolate()
                + &(&v_H * w_rand).into();
            let (w_poly, remainder) = w_poly.divide_by_vanishing_poly(domain_x).unwrap();
            assert!(remainder.is_zero());
            w_poly
        });

        end_timer!(w_poly_time);

        let r_a = F::rand(rng);
        let z_a = state.z_a.clone().unwrap();
        job_pool.add_job(|| {
            let z_a_poly_time = start_timer!(|| "Computing z_A polynomial");
            let mut z_a_poly = EvaluationsOnDomain::from_vec_and_domain(z_a, domain_h).interpolate();
            if MM::ZK {
                z_a_poly += &(&v_H * r_a);
            }
            end_timer!(z_a_poly_time);
            z_a_poly
        });

        let r_b = F::rand(rng);
        let z_b = state.z_b.clone().unwrap();
        job_pool.add_job(|| {
            let z_b_poly_time = start_timer!(|| "Computing z_B polynomial");
            let mut z_b_poly = EvaluationsOnDomain::from_vec_and_domain(z_b, domain_h).interpolate();
            if MM::ZK {
                z_b_poly += &(&v_H * r_b);
            }
            end_timer!(z_b_poly_time);
            z_b_poly
        });
        let [w_poly, z_a_poly, z_b_poly]: [Polynomial<F>; 3] = job_pool.execute_all().try_into().unwrap();

        let mask_poly = if MM::ZK {
            let mask_poly_time = start_timer!(|| "Computing mask polynomial");
            // We'll use the masking technique from Lunar (https://eprint.iacr.org/2020/1069.pdf, pgs 20-22).
            let h_1_mask = Polynomial::rand(3, rng).coeffs; // selected arbitrarily.
            let h_1_mask: Polynomial<_> =
                SparsePolynomial::from_coefficients_vec(h_1_mask.into_iter().enumerate().collect())
                    .mul(&domain_h.vanishing_polynomial())
                    .into();
            assert_eq!(h_1_mask.degree(), domain_h.size() + 3);
            // multiply g_1_mask by X
            let mut g_1_mask = Polynomial::rand(5, rng);
            g_1_mask.coeffs[0] = F::zero();

            let mut mask_poly = h_1_mask;
            mask_poly += &g_1_mask;
            end_timer!(mask_poly_time);
            debug_assert!(domain_h.elements().map(|z| mask_poly.evaluate(z)).sum::<F>().is_zero());
            assert_eq!(mask_poly.degree(), domain_h.size() + 3);
            assert!(mask_poly.degree() <= 3 * domain_h.size() + 2 * zk_bound - 3);
            Some(mask_poly)
        } else {
            None
        };

        let msg = ProverMessage::default();

        assert!(w_poly.degree() < domain_h.size() - domain_x.size() + zk_bound);
        assert!(z_a_poly.degree() < domain_h.size() + zk_bound);
        assert!(z_b_poly.degree() < domain_h.size() + zk_bound);

        let hiding_bound = if MM::ZK { Some(1) } else { None };

        let w = LabeledPolynomial::new("w".to_string(), w_poly, None, hiding_bound);
        let z_a = LabeledPolynomial::new("z_a".to_string(), z_a_poly, None, hiding_bound);
        let z_b = LabeledPolynomial::new("z_b".to_string(), z_b_poly, None, hiding_bound);

        let mask_poly =
            mask_poly.map(|mask_poly| LabeledPolynomial::new("mask_poly".to_string(), mask_poly, None, None));

        let oracles = ProverFirstOracles {
            w: w.clone(),
            z_a: z_a.clone(),
            z_b: z_b.clone(),
            mask_poly: mask_poly.clone(),
        };

        state.w_poly = Some(w);
        state.mz_polys = Some((z_a, z_b));
        state.mz_poly_randomizer = Some((r_a, r_b));
        state.mask_poly = mask_poly;
        end_timer!(round_time);

        Ok((msg, oracles, state))
    }

    fn calculate_t<'a>(
        matrices: impl Iterator<Item = &'a Matrix<F>>,
        matrix_randomizers: &[F],
        input_domain: EvaluationDomain<F>,
        domain_h: EvaluationDomain<F>,
        r_alpha_x_on_h: &Vec<F>,
    ) -> Polynomial<F> {
        let mut t_evals_on_h = vec![F::zero(); domain_h.size()];
        for (matrix, eta) in matrices.zip(matrix_randomizers) {
            for (r, row) in matrix.iter().enumerate() {
                for (coeff, c) in row.iter() {
                    let index = domain_h.reindex_by_subdomain(input_domain, *c);
                    t_evals_on_h[index] += &(*eta * coeff * r_alpha_x_on_h[r]);
                }
            }
        }
        EvaluationsOnDomain::from_vec_and_domain(t_evals_on_h, domain_h).interpolate()
    }

    /// Output the number of oracles sent by the prover in the first round.
    pub fn prover_num_first_round_oracles() -> usize {
        if MM::ZK { 4 } else { 3 }
    }

    /// Output the degree bounds of oracles in the first round.
    pub fn prover_first_round_degree_bounds(_info: &CircuitInfo<F>) -> impl Iterator<Item = Option<usize>> {
        if MM::ZK {
            vec![None; 4].into_iter()
        } else {
            vec![None; 3].into_iter()
        }
    }

    /// Output the second round message and the next state.
    pub fn prover_second_round<'a, R: RngCore>(
        verifier_message: &VerifierFirstMessage<F>,
        mut state: ProverState<'a, F, MM>,
        _r: &mut R,
    ) -> (ProverMessage<F>, ProverSecondOracles<F>, ProverState<'a, F, MM>) {
        let round_time = start_timer!(|| "AHP::Prover::SecondRound");

        let domain_h = state.domain_h;
        let zk_bound = state.zk_bound;

        let mask_poly = state.mask_poly.as_ref();
        assert_eq!(MM::ZK, mask_poly.is_some());

        let VerifierFirstMessage {
            alpha,
            eta_a,
            eta_b,
            eta_c,
        } = *verifier_message;

        let summed_z_m_poly_time = start_timer!(|| "Compute z_m poly");
        let (z_a_poly, z_b_poly) = state.mz_polys.as_ref().unwrap();
        if MM::ZK {
            assert_eq!(z_a_poly.degree(), domain_h.size());
            assert_eq!(z_b_poly.degree(), domain_h.size());
        } else {
            assert!(z_a_poly.degree() < domain_h.size());
            assert!(z_b_poly.degree() < domain_h.size());
        }
        let (z_a_poly, z_b_poly) = state.mz_polys.as_ref().unwrap();
        let (r_a, r_b) = state.mz_poly_randomizer.as_ref().unwrap();

        let z_c_poly = if MM::ZK {
            let v_H = domain_h.vanishing_polynomial();
            let r_a_v_H = v_H.mul(&SparsePolynomial::from_coefficients_slice(&[(0, *r_a)]));
            let r_b_v_H = v_H.mul(&SparsePolynomial::from_coefficients_slice(&[(0, *r_b)]));
            let z_a_poly_det = z_a_poly.polynomial().clone() - &r_a_v_H;
            let z_b_poly_det = z_b_poly.polynomial().clone() - &r_b_v_H;
            // z_c = (z_a + r_a * v_H) * (z_b + r_b * v_H);
            // z_c = z_a * z_b + r_a * z_b * v_H + r_b * z_a * v_H + r_a * r_b * v_H^2;
            let mut z_c = &z_a_poly_det * &z_b_poly_det;
            z_c += &r_a_v_H.mul(&r_b_v_H);
            assert_eq!(z_c.degree(), 2 * domain_h.size());
            #[cfg(not(feature = "parallel"))]
            use core::iter::repeat;
            #[cfg(feature = "parallel")]
            use rayon::iter::repeat;

            let zero = F::zero();
            repeat(&zero)
                .take(domain_h.size())
                .chain(&z_a_poly_det.coeffs)
                .enumerate()
                .zip(&mut z_c.coeffs)
                .for_each(|((i, c), z_c)| {
                    let t = if i < domain_h.size() {
                        z_a_poly_det.coeffs.get(i).map_or(F::zero(), |c| -*c)
                    } else {
                        *c
                    };
                    *z_c += t * r_b;
                });
            repeat(&zero)
                .take(domain_h.size())
                .chain(&z_b_poly_det.coeffs)
                .enumerate()
                .zip(&mut z_c.coeffs)
                .for_each(|((i, c), z_c)| {
                    let t = if i < domain_h.size() {
                        z_b_poly_det.coeffs.get(i).map_or(F::zero(), |c| -*c)
                    } else {
                        *c
                    };
                    *z_c += t * r_a;
                });
            z_c
        } else {
            z_a_poly.polynomial() * z_b_poly.polynomial()
        };

        let r_alpha_x_evals_time = start_timer!(|| "Compute r_alpha_x evals");
        let r_alpha_x_evals = domain_h.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(alpha);
        end_timer!(r_alpha_x_evals_time);

        let mut job_pool = snarkvm_utilities::ExecutionPool::with_capacity(2);
        job_pool.add_job(|| {
            let mut summed_z_m_coeffs = z_c_poly.coeffs;
            // Note: Can't combine these two loops, because z_c_poly has 2x the degree
            // of z_a_poly and z_b_poly, so the second loop gets truncated due to
            // the `zip`s.
            cfg_iter_mut!(summed_z_m_coeffs).for_each(|c| *c *= &eta_c);
            cfg_iter_mut!(summed_z_m_coeffs)
                .zip(&z_a_poly.polynomial().coeffs)
                .zip(&z_b_poly.polynomial().coeffs)
                .for_each(|((c, a), b)| *c += eta_a * a + eta_b * b);

            let summed_z_m = Polynomial::from_coefficients_vec(summed_z_m_coeffs);
            end_timer!(summed_z_m_poly_time);
            summed_z_m
        });

        job_pool.add_job(|| {
            let r_alpha_poly_time = start_timer!(|| "Compute r_alpha_x poly");
            let r_alpha_poly = Polynomial::from_coefficients_vec(domain_h.ifft(&r_alpha_x_evals));
            end_timer!(r_alpha_poly_time);
            r_alpha_poly
        });

        job_pool.add_job(|| {
            let t_poly_time = start_timer!(|| "Compute t poly");
            let t_poly = Self::calculate_t(
                vec![&state.index.a, &state.index.b, &state.index.c].into_iter(),
                &[eta_a, eta_b, eta_c],
                state.domain_x,
                state.domain_h,
                &r_alpha_x_evals,
            );
            end_timer!(t_poly_time);
            t_poly
        });
        let [summed_z_m, r_alpha_poly, t_poly]: [Polynomial<F>; 3] = job_pool.execute_all().try_into().unwrap();

        let z_poly_time = start_timer!(|| "Compute z poly");

        let x_poly = EvaluationsOnDomain::from_vec_and_domain(state.padded_public_variables.clone(), state.domain_x)
            .interpolate();
        let w_poly = state.w_poly.as_ref().unwrap();
        let mut z_poly = w_poly.polynomial().mul_by_vanishing_poly(state.domain_x);
        cfg_iter_mut!(z_poly.coeffs)
            .zip(&x_poly.coeffs)
            .for_each(|(z, x)| *z += x);
        assert!(z_poly.degree() < domain_h.size() + zk_bound);

        end_timer!(z_poly_time);

        let q_1_time = start_timer!(|| "Compute q_1 poly");

        let mul_domain_size = *[
            mask_poly.map_or(0, |p| p.len()),
            r_alpha_poly.coeffs.len() + summed_z_m.coeffs.len(),
            t_poly.coeffs.len() + z_poly.len(),
        ]
        .iter()
        .max()
        .unwrap();
        let mul_domain =
            EvaluationDomain::new(mul_domain_size).expect("field is not smooth enough to construct domain");
        let mut job_pool = snarkvm_utilities::ExecutionPool::with_capacity(4);
        job_pool.add_job(|| r_alpha_poly.evaluate_over_domain_by_ref(mul_domain));
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
        rhs += mask_poly.map_or(&Polynomial::zero(), |p| p.polynomial());
        let q_1 = rhs;
        end_timer!(q_1_time);

        let sumcheck_time = start_timer!(|| "Compute sumcheck h and g polys");
        let (h_1, x_g_1) = q_1.divide_by_vanishing_poly(domain_h).unwrap();
        let g_1 = Polynomial::from_coefficients_slice(&x_g_1.coeffs[1..]);
        end_timer!(sumcheck_time);

        let msg = ProverMessage::default();

        assert!(g_1.degree() <= domain_h.size() - 2);
        assert!(h_1.degree() <= 2 * domain_h.size() + 2 * zk_bound - 2);

        let hiding_bound = if MM::ZK { Some(1) } else { None };
        let oracles = ProverSecondOracles {
            t: LabeledPolynomial::new("t".into(), t_poly, None, None),
            g_1: LabeledPolynomial::new("g_1".into(), g_1, Some(domain_h.size() - 2), hiding_bound),
            h_1: LabeledPolynomial::new("h_1".into(), h_1, None, None),
        };

        state.w_poly = None;
        state.verifier_first_message = Some(*verifier_message);
        end_timer!(round_time);

        (msg, oracles, state)
    }

    /// Output the number of oracles sent by the prover in the second round.
    pub fn prover_num_second_round_oracles() -> usize {
        3
    }

    /// Output the degree bounds of oracles in the second round.
    pub fn prover_second_round_degree_bounds(info: &CircuitInfo<F>) -> impl Iterator<Item = Option<usize>> {
        let h_domain_size = EvaluationDomain::<F>::compute_size_of_domain(info.num_constraints).unwrap();

        vec![None, Some(h_domain_size - 2), None].into_iter()
    }

    /// Output the third round message and the next state.
    pub fn prover_third_round<'a, R: RngCore>(
        verifier_message: &VerifierSecondMessage<F>,
        prover_state: ProverState<'a, F, MM>,
        _r: &mut R,
    ) -> Result<(ProverMessage<F>, ProverThirdOracles<F>), AHPError> {
        let round_time = start_timer!(|| "AHP::Prover::ThirdRound");

        let ProverState {
            index,
            verifier_first_message,
            domain_h,
            domain_k,
            ..
        } = prover_state;

        let VerifierFirstMessage {
            eta_a,
            eta_b,
            eta_c,
            alpha,
        } = verifier_first_message
            .expect("ProverState should include verifier_first_msg when prover_third_round is called");

        let beta = verifier_message.beta;

        let v_H_at_alpha = domain_h.evaluate_vanishing_polynomial(alpha);
        let v_H_at_beta = domain_h.evaluate_vanishing_polynomial(beta);

        let v_H_alpha_v_H_beta = v_H_at_alpha * v_H_at_beta;
        let eta_a_times_v_H_alpha_v_H_beta = eta_a * v_H_alpha_v_H_beta;
        let eta_b_times_v_H_alpha_v_H_beta = eta_b * v_H_alpha_v_H_beta;
        let eta_c_times_v_H_alpha_v_H_beta = eta_c * v_H_alpha_v_H_beta;

        let joint_arith = &index.joint_arith;

        let a_poly_time = start_timer!(|| "Computing a poly");
        let a_poly = {
            let a = joint_arith.val_a.coeffs();
            let b = joint_arith.val_b.coeffs();
            let c = joint_arith.val_c.coeffs();
            let coeffs: Vec<F> = cfg_iter!(a)
                .zip(b)
                .zip(c)
                .map(|((a, b), c)| {
                    eta_a_times_v_H_alpha_v_H_beta * a
                        + eta_b_times_v_H_alpha_v_H_beta * b
                        + eta_c_times_v_H_alpha_v_H_beta * c
                })
                .collect();
            DensePolynomial::from_coefficients_vec(coeffs)
        };
        end_timer!(a_poly_time);

        let (row_on_K, col_on_K, row_col_on_K) = (
            &joint_arith.evals_on_K.row,
            &joint_arith.evals_on_K.col,
            &joint_arith.evals_on_K.row_col,
        );

        let b_poly_time = start_timer!(|| "Computing b poly");
        let alpha_beta = alpha * beta;
        let b_poly = {
            let evals: Vec<F> = cfg_iter!(row_on_K.evaluations)
                .zip(&col_on_K.evaluations)
                .zip(&row_col_on_K.evaluations)
                .map(|((r, c), r_c)| alpha_beta - alpha * r - beta * c + r_c)
                .collect();
            EvaluationsOnDomain::from_vec_and_domain(evals, domain_k).interpolate()
        };
        end_timer!(b_poly_time);

        let f_evals_time = start_timer!(|| "Computing f evals on K");
        let mut inverses: Vec<_> = cfg_into_iter!(0..domain_k.size())
            .map(|i| (beta - row_on_K[i]) * (alpha - col_on_K[i]))
            .collect();
        batch_inversion(&mut inverses);

        let (val_a_on_K, val_b_on_K, val_c_on_K) = (
            &joint_arith.evals_on_K.val_a,
            &joint_arith.evals_on_K.val_b,
            &joint_arith.evals_on_K.val_c,
        );
        let f_evals_on_K: Vec<_> = cfg_into_iter!(0..(domain_k.size()))
            .map(|i| {
                inverses[i]
                    * (eta_a_times_v_H_alpha_v_H_beta * val_a_on_K[i]
                        + eta_b_times_v_H_alpha_v_H_beta * val_b_on_K[i]
                        + eta_c_times_v_H_alpha_v_H_beta * val_c_on_K[i])
            })
            .collect();
        end_timer!(f_evals_time);

        let f_poly_time = start_timer!(|| "Computing f poly");
        let f = EvaluationsOnDomain::from_vec_and_domain(f_evals_on_K, domain_k).interpolate();
        end_timer!(f_poly_time);

        let h_2_poly_time = start_timer!(|| "Computing sumcheck h poly");
        let h_2 = (&a_poly - &(&b_poly * &f))
            .divide_by_vanishing_poly(domain_k)
            .unwrap()
            .0;
        end_timer!(h_2_poly_time);
        drop(a_poly);
        drop(b_poly);
        let g_2 = DensePolynomial::from_coefficients_slice(&f.coeffs[1..]);
        drop(f);

        let msg = ProverMessage::default();

        assert!(h_2.degree() <= domain_k.size() - 2);
        assert!(g_2.degree() <= domain_k.size() - 2);

        let oracles = ProverThirdOracles {
            g_2: LabeledPolynomial::new("g_2".to_string(), g_2, Some(domain_k.size() - 2), None),
            h_2: LabeledPolynomial::new("h_2".to_string(), h_2, None, None),
        };
        end_timer!(round_time);

        Ok((msg, oracles))
    }

    /// Output the number of oracles sent by the prover in the third round.
    pub fn prover_num_third_round_oracles() -> usize {
        2
    }

    /// Output the degree bounds of oracles in the third round.
    pub fn prover_third_round_degree_bounds(info: &CircuitInfo<F>) -> impl Iterator<Item = Option<usize>> {
        let num_non_zero = info.num_non_zero;
        let k_size = EvaluationDomain::<F>::compute_size_of_domain(num_non_zero).unwrap();

        vec![Some(k_size - 2), None].into_iter()
    }
}
