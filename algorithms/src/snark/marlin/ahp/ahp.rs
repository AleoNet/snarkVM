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

use crate::{
    fft::{
        domain::{FFTPrecomputation, IFFTPrecomputation},
        EvaluationDomain,
    },
    polycommit::sonic_pc::{LCTerm, LabeledPolynomial, LinearCombination},
    snark::marlin::{
        ahp::{matrices, verifier, AHPError, CircuitInfo},
        prover,
        MarlinMode,
    },
};
use itertools::Itertools;
use snarkvm_fields::{Field, PrimeField};

use core::{borrow::Borrow, marker::PhantomData};
use std::collections::BTreeMap;

/// The algebraic holographic proof defined in [CHMMVW19](https://eprint.iacr.org/2019/1047).
/// Currently, this AHP only supports inputs of size one
/// less than a power of 2 (i.e., of the form 2^n - 1).
pub struct AHPForR1CS<F: Field, MM: MarlinMode> {
    field: PhantomData<F>,
    mode: PhantomData<MM>,
}

pub(crate) fn witness_label(poly: &str, i: usize) -> String {
    format!("{poly}_{:0>8}", i)
}

impl<F: PrimeField, MM: MarlinMode> AHPForR1CS<F, MM> {
    /// The linear combinations that are statically known to evaluate to zero.
    #[rustfmt::skip]
    pub const LC_WITH_ZERO_EVAL: [&'static str; 2] = ["matrix_sumcheck", "lincheck_sumcheck"];

    pub fn zk_bound() -> Option<usize> {
        MM::ZK.then(|| 1)
    }

    /// Check that the (formatted) public input is of the form 2^n for some integer n.
    pub fn num_formatted_public_inputs_is_admissible(num_inputs: usize) -> Result<(), AHPError> {
        match num_inputs.count_ones() == 1 {
            true => Ok(()),
            false => Err(AHPError::InvalidPublicInputLength),
        }
    }

    /// Check that the (formatted) public input is of the form 2^n for some integer n.
    pub fn formatted_public_input_is_admissible(input: &[F]) -> Result<(), AHPError> {
        Self::num_formatted_public_inputs_is_admissible(input.len())
    }

    /// The maximum degree of polynomials produced by the indexer and prover
    /// of this protocol.
    /// The number of the variables must include the "one" variable. That is, it
    /// must be with respect to the number of formatted public inputs.
    pub fn max_degree(num_constraints: usize, num_variables: usize, num_non_zero: usize) -> Result<usize, AHPError> {
        let padded_matrix_dim = matrices::padded_matrix_dim(num_variables, num_constraints);
        let zk_bound = 1;
        let constraint_domain_size = EvaluationDomain::<F>::compute_size_of_domain(padded_matrix_dim)
            .ok_or(AHPError::PolynomialDegreeTooLarge)?;
        let non_zero_domain_size =
            EvaluationDomain::<F>::compute_size_of_domain(num_non_zero).ok_or(AHPError::PolynomialDegreeTooLarge)?;

        Ok(*[
            2 * constraint_domain_size + zk_bound - 2,
            if MM::ZK { 3 * constraint_domain_size + 2 * zk_bound - 3 } else { 0 }, //  mask_poly
            constraint_domain_size,
            constraint_domain_size,
            non_zero_domain_size - 1,
            non_zero_domain_size, //  due to vanishing polynomial; for convenience, we increase the number by one regardless of the mode.
        ]
        .iter()
        .max()
        .unwrap())
    }

    /// Get all the strict degree bounds enforced in the AHP.
    pub fn get_degree_bounds(info: &CircuitInfo<F>) -> [usize; 4] {
        let num_constraints = info.num_constraints;
        let num_non_zero_a = info.num_non_zero_a;
        let num_non_zero_b = info.num_non_zero_b;
        let num_non_zero_c = info.num_non_zero_c;
        [
            EvaluationDomain::<F>::compute_size_of_domain(num_constraints).unwrap() - 2,
            EvaluationDomain::<F>::compute_size_of_domain(num_non_zero_a).unwrap() - 2,
            EvaluationDomain::<F>::compute_size_of_domain(num_non_zero_b).unwrap() - 2,
            EvaluationDomain::<F>::compute_size_of_domain(num_non_zero_c).unwrap() - 2,
        ]
    }

    pub fn max_non_zero_domain(info: &CircuitInfo<F>) -> EvaluationDomain<F> {
        let non_zero_a_domain = EvaluationDomain::new(info.num_non_zero_a).unwrap();
        let non_zero_b_domain = EvaluationDomain::new(info.num_non_zero_b).unwrap();
        let non_zero_c_domain = EvaluationDomain::new(info.num_non_zero_c).unwrap();
        Self::max_non_zero_domain_helper(non_zero_a_domain, non_zero_b_domain, non_zero_c_domain)
    }

    fn max_non_zero_domain_helper(
        domain_a: EvaluationDomain<F>,
        domain_b: EvaluationDomain<F>,
        domain_c: EvaluationDomain<F>,
    ) -> EvaluationDomain<F> {
        [domain_a, domain_b, domain_c].into_iter().max_by_key(|d| d.size()).unwrap()
    }

    pub fn fft_precomputation(
        constraint_domain_size: usize,
        non_zero_a_domain_size: usize,
        non_zero_b_domain_size: usize,
        non_zero_c_domain_size: usize,
    ) -> Option<(FFTPrecomputation<F>, IFFTPrecomputation<F>)> {
        let largest_domain_size = [
            3 * constraint_domain_size,
            non_zero_a_domain_size * 2,
            non_zero_b_domain_size * 2,
            non_zero_c_domain_size * 2,
        ]
        .into_iter()
        .max()?;
        let largest_mul_domain = EvaluationDomain::new(largest_domain_size)?;

        let fft_precomputation = largest_mul_domain.precompute_fft();
        let ifft_precomputation = fft_precomputation.to_ifft_precomputation();
        Some((fft_precomputation, ifft_precomputation))
    }

    /// Construct the linear combinations that are checked by the AHP.
    /// Public input should be unformatted.
    #[allow(non_snake_case)]
    pub fn construct_linear_combinations<E: EvaluationsProvider<F>>(
        public_inputs: &[Vec<F>],
        evals: &E,
        prover_third_message: &prover::ThirdMessage<F>,
        state: &verifier::State<F, MM>,
    ) -> Result<BTreeMap<String, LinearCombination<F>>, AHPError> {
        assert!(!public_inputs.is_empty());
        let constraint_domain = state.constraint_domain;

        let non_zero_a_domain = state.non_zero_a_domain;
        let non_zero_b_domain = state.non_zero_b_domain;
        let non_zero_c_domain = state.non_zero_c_domain;

        let largest_non_zero_domain =
            Self::max_non_zero_domain_helper(state.non_zero_a_domain, state.non_zero_b_domain, state.non_zero_c_domain);

        let public_inputs = public_inputs
            .iter()
            .map(|p| {
                let public_input = prover::ConstraintSystem::format_public_input(p);
                Self::formatted_public_input_is_admissible(&public_input).map(|_| public_input)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let input_domain = EvaluationDomain::new(public_inputs[0].len()).ok_or(AHPError::PolynomialDegreeTooLarge)?;

        let first_round_msg = state.first_round_message.as_ref().unwrap();
        let alpha = first_round_msg.alpha;
        let eta_a = F::one();
        let eta_b = first_round_msg.eta_b;
        let eta_c = first_round_msg.eta_c;
        let batch_combiners = &first_round_msg.batch_combiners;
        let prover::ThirdMessage { sum_a, sum_b, sum_c } = prover_third_message;

        #[rustfmt::skip]
        let t_at_beta =
            eta_a * state.non_zero_a_domain.size_as_field_element * sum_a +
            eta_b * state.non_zero_b_domain.size_as_field_element * sum_b +
            eta_c * state.non_zero_c_domain.size_as_field_element * sum_c;
        let r_b = state.third_round_message.as_ref().unwrap().r_b;
        let r_c = state.third_round_message.as_ref().unwrap().r_c;

        let beta = state.second_round_message.unwrap().beta;
        let gamma = state.gamma.unwrap();

        let mut linear_combinations = BTreeMap::new();

        // Lincheck sumcheck:
        let z_b_s = (0..state.batch_size)
            .map(|i| {
                let z_b_i = witness_label("z_b", i);
                LinearCombination::new(z_b_i.clone(), [(F::one(), z_b_i)])
            })
            .collect::<Vec<_>>();
        let g_1 = LinearCombination::new("g_1", [(F::one(), "g_1")]);

        let r_alpha_at_beta = constraint_domain.eval_unnormalized_bivariate_lagrange_poly(alpha, beta);
        let v_H_at_alpha = constraint_domain.evaluate_vanishing_polynomial(alpha);
        let v_H_at_beta = constraint_domain.evaluate_vanishing_polynomial(beta);
        let v_X_at_beta = input_domain.evaluate_vanishing_polynomial(beta);

        let z_b_s_at_beta = z_b_s.iter().map(|z_b| evals.get_lc_eval(z_b, beta)).collect::<Result<Vec<_>, _>>()?;
        let batch_z_b_at_beta: F =
            z_b_s_at_beta.iter().zip_eq(batch_combiners).map(|(z_b_at_beta, combiner)| *z_b_at_beta * combiner).sum();
        let g_1_at_beta = evals.get_lc_eval(&g_1, beta)?;

        let lag_at_beta = input_domain.evaluate_all_lagrange_coefficients(beta);
        let combined_x_at_beta = batch_combiners
            .iter()
            .zip_eq(&public_inputs)
            .map(|(c, x)| x.iter().zip_eq(&lag_at_beta).map(|(x, l)| *x * l).sum::<F>() * c)
            .sum::<F>();

        #[rustfmt::skip]
        let lincheck_sumcheck = {
            let mut lincheck_sumcheck = LinearCombination::empty("lincheck_sumcheck");
            if MM::ZK {
                lincheck_sumcheck.add(F::one(), "mask_poly");
            }
            for (i, (z_b_i_at_beta, combiner)) in z_b_s_at_beta.iter().zip_eq(batch_combiners).enumerate() {
                lincheck_sumcheck
                    .add(r_alpha_at_beta * combiner * (eta_a + eta_c * z_b_i_at_beta), witness_label("z_a", i))
                    .add(-t_at_beta * v_X_at_beta * combiner, witness_label("w", i));
            }
            lincheck_sumcheck
                .add(r_alpha_at_beta * eta_b * batch_z_b_at_beta, LCTerm::One)
                .add(-t_at_beta * combined_x_at_beta, LCTerm::One)
                .add(-v_H_at_beta, "h_1")
                .add(-beta * g_1_at_beta, LCTerm::One);
            lincheck_sumcheck
        };
        debug_assert!(evals.get_lc_eval(&lincheck_sumcheck, beta)?.is_zero());

        for z_b in z_b_s {
            linear_combinations.insert(z_b.label.clone(), z_b);
        }
        linear_combinations.insert("g_1".into(), g_1);
        linear_combinations.insert("lincheck_sumcheck".into(), lincheck_sumcheck);

        //  Matrix sumcheck:
        let mut matrix_sumcheck = LinearCombination::empty("matrix_sumcheck");

        let g_a = LinearCombination::new("g_a", [(F::one(), "g_a")]);
        let g_a_at_gamma = evals.get_lc_eval(&g_a, gamma)?;
        let selector_a = largest_non_zero_domain.evaluate_selector_polynomial(non_zero_a_domain, gamma);
        let lhs_a =
            Self::construct_lhs("a", alpha, beta, gamma, v_H_at_alpha * v_H_at_beta, g_a_at_gamma, *sum_a, selector_a);
        matrix_sumcheck += &lhs_a;

        let g_b = LinearCombination::new("g_b", [(F::one(), "g_b")]);
        let g_b_at_gamma = evals.get_lc_eval(&g_b, gamma)?;
        let selector_b = largest_non_zero_domain.evaluate_selector_polynomial(non_zero_b_domain, gamma);
        let lhs_b =
            Self::construct_lhs("b", alpha, beta, gamma, v_H_at_alpha * v_H_at_beta, g_b_at_gamma, *sum_b, selector_b);
        matrix_sumcheck += (r_b, &lhs_b);

        let g_c = LinearCombination::new("g_c", [(F::one(), "g_c")]);
        let g_c_at_gamma = evals.get_lc_eval(&g_c, gamma)?;
        let selector_c = largest_non_zero_domain.evaluate_selector_polynomial(non_zero_c_domain, gamma);
        let lhs_c =
            Self::construct_lhs("c", alpha, beta, gamma, v_H_at_alpha * v_H_at_beta, g_c_at_gamma, *sum_c, selector_c);
        matrix_sumcheck += (r_c, &lhs_c);

        matrix_sumcheck -=
            &LinearCombination::new("h_2", [(largest_non_zero_domain.evaluate_vanishing_polynomial(gamma), "h_2")]);
        debug_assert!(evals.get_lc_eval(&matrix_sumcheck, gamma)?.is_zero());

        linear_combinations.insert("g_a".into(), g_a);
        linear_combinations.insert("g_b".into(), g_b);
        linear_combinations.insert("g_c".into(), g_c);
        linear_combinations.insert("matrix_sumcheck".into(), matrix_sumcheck);

        Ok(linear_combinations)
    }

    #[allow(clippy::too_many_arguments)]
    fn construct_lhs(
        label: &str,
        alpha: F,
        beta: F,
        gamma: F,
        v_h_at_alpha_beta: F,
        g_at_gamma: F,
        sum: F,
        selector_at_gamma: F,
    ) -> LinearCombination<F> {
        let a =
            LinearCombination::new("a_poly_".to_string() + label, [(v_h_at_alpha_beta, "val_".to_string() + label)]);
        let alpha_beta = alpha * beta;

        let mut b = LinearCombination::new("denom_".to_string() + label, [
            (alpha_beta, LCTerm::One),
            (-alpha, ("row_".to_string() + label).into()),
            (-beta, ("col_".to_string() + label).into()),
            (F::one(), ("row_col_".to_string() + label).into()),
        ]);
        b *= gamma * g_at_gamma + sum;

        let mut lhs = a;
        lhs -= &b;
        lhs *= selector_at_gamma;
        lhs
    }
}

/// Abstraction that provides evaluations of (linear combinations of) polynomials
///
/// Intended to provide a common interface for both the prover and the verifier
/// when constructing linear combinations via `AHPForR1CS::construct_linear_combinations`.
pub trait EvaluationsProvider<F: PrimeField>: core::fmt::Debug {
    /// Get the evaluation of linear combination `lc` at `point`.
    fn get_lc_eval(&self, lc: &LinearCombination<F>, point: F) -> Result<F, AHPError>;
}

impl<'a, F: PrimeField> EvaluationsProvider<F> for crate::polycommit::sonic_pc::Evaluations<'a, F> {
    fn get_lc_eval(&self, lc: &LinearCombination<F>, point: F) -> Result<F, AHPError> {
        let key = (lc.label.clone(), point);
        self.get(&key).copied().ok_or_else(|| AHPError::MissingEval(lc.label.clone()))
    }
}

impl<F, T> EvaluationsProvider<F> for Vec<T>
where
    F: PrimeField,
    T: Borrow<LabeledPolynomial<F>> + core::fmt::Debug,
{
    fn get_lc_eval(&self, lc: &LinearCombination<F>, point: F) -> Result<F, AHPError> {
        let mut eval = F::zero();
        for (coeff, term) in lc.iter() {
            let value = if let LCTerm::PolyLabel(label) = term {
                self.iter()
                    .find(|p| (*p).borrow().label() == label)
                    .ok_or_else(|| AHPError::MissingEval(format!("Missing {} for {}", label, lc.label)))?
                    .borrow()
                    .evaluate(point)
            } else {
                assert!(term.is_one());
                F::one()
            };
            eval += &(*coeff * value)
        }
        Ok(eval)
    }
}

/// The derivative of the vanishing polynomial
pub trait UnnormalizedBivariateLagrangePoly<F: PrimeField> {
    /// Evaluate the polynomial
    fn eval_unnormalized_bivariate_lagrange_poly(&self, x: F, y: F) -> F;

    /// Evaluate over a batch of inputs
    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(&self, x: F) -> Vec<F>;

    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs_over_domain(
        &self,
        x: F,
        domain: &EvaluationDomain<F>,
    ) -> Vec<F>;

    /// Evaluate the magic polynomial over `self`
    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs(&self) -> Vec<F>;
}

impl<F: PrimeField> UnnormalizedBivariateLagrangePoly<F> for EvaluationDomain<F> {
    fn eval_unnormalized_bivariate_lagrange_poly(&self, x: F, y: F) -> F {
        if x != y {
            (self.evaluate_vanishing_polynomial(x) - self.evaluate_vanishing_polynomial(y)) / (x - y)
        } else {
            self.size_as_field_element * x.pow(&[(self.size() - 1) as u64])
        }
    }

    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs_over_domain(
        &self,
        x: F,
        domain: &EvaluationDomain<F>,
    ) -> Vec<F> {
        use snarkvm_utilities::{cfg_iter, cfg_iter_mut};

        #[cfg(feature = "parallel")]
        use rayon::prelude::*;

        let vanish_x = self.evaluate_vanishing_polynomial(x);
        let elements = domain.elements().collect::<Vec<_>>();

        let mut denoms = cfg_iter!(elements).map(|e| x - e).collect::<Vec<_>>();
        if domain.size() <= self.size() {
            snarkvm_fields::batch_inversion_and_mul(&mut denoms, &vanish_x);
        } else {
            snarkvm_fields::batch_inversion(&mut denoms);
            let ratio = domain.size() / self.size();
            let mut numerators = vec![vanish_x; domain.size()];
            cfg_iter_mut!(numerators).zip_eq(elements).enumerate().for_each(|(i, (n, e))| {
                if i % ratio != 0 {
                    *n -= self.evaluate_vanishing_polynomial(e);
                }
            });
            cfg_iter_mut!(denoms).zip_eq(numerators).for_each(|(d, e)| *d *= e);
        }
        denoms
    }

    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(&self, x: F) -> Vec<F> {
        self.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs_over_domain(x, self)
    }

    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs(&self) -> Vec<F> {
        let mut elems: Vec<F> = self.elements().map(|e| e * self.size_as_field_element).collect();
        elems[1..].reverse();
        elems
    }
}

/// Given two domains H and K such that H \subseteq K,
/// construct polynomial that outputs 0 on all elements in K \ H, but 1 on all elements of H.
pub trait SelectorPolynomial<F: PrimeField> {
    fn evaluate_selector_polynomial(&self, other: EvaluationDomain<F>, point: F) -> F;
}

impl<F: PrimeField> SelectorPolynomial<F> for EvaluationDomain<F> {
    fn evaluate_selector_polynomial(&self, other: EvaluationDomain<F>, point: F) -> F {
        let numerator = self.evaluate_vanishing_polynomial(point) * other.size_as_field_element;
        let denominator = other.evaluate_vanishing_polynomial(point) * self.size_as_field_element;
        numerator / denominator
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fft::{DensePolynomial, Evaluations};
    use snarkvm_curves::bls12_377::fr::Fr;
    use snarkvm_fields::{One, Zero};
    use snarkvm_utilities::rand::{test_rng, Uniform};

    #[test]
    fn domain_unnormalized_bivariate_lagrange_poly() {
        for domain_size in 1..10 {
            let domain = EvaluationDomain::<Fr>::new(1 << domain_size).unwrap();
            let manual: Vec<_> =
                domain.elements().map(|elem| domain.eval_unnormalized_bivariate_lagrange_poly(elem, elem)).collect();
            let fast = domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs();
            assert_eq!(fast, manual);
        }
    }

    #[test]
    fn domain_unnormalized_bivariate_lagrange_poly_diff_inputs() {
        let rng = &mut test_rng();
        for domain_size in 1..10 {
            let domain = EvaluationDomain::<Fr>::new(1 << domain_size).unwrap();
            let x = Fr::rand(rng);
            let manual: Vec<_> =
                domain.elements().map(|y| domain.eval_unnormalized_bivariate_lagrange_poly(x, y)).collect();
            let fast = domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(x);
            assert_eq!(fast, manual);
        }
    }

    #[test]
    fn domain_unnormalized_bivariate_lagrange_poly_diff_inputs_over_domain() {
        let rng = &mut test_rng();
        for domain_size in 1..10 {
            let domain = EvaluationDomain::<Fr>::new(1 << domain_size).unwrap();
            let x = Fr::rand(rng);
            for other_domain_size in 1..10 {
                let other = EvaluationDomain::<Fr>::new(1 << other_domain_size).unwrap();
                let manual: Vec<_> =
                    other.elements().map(|y| domain.eval_unnormalized_bivariate_lagrange_poly(x, y)).collect();
                let fast =
                    domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs_over_domain(x, &other);
                assert_eq!(fast, manual, "failed for self {:?} and other {:?}", domain, other);
            }
        }
    }

    #[test]
    fn test_summation() {
        let rng = &mut test_rng();
        let size = 1 << 4;
        let domain = EvaluationDomain::<Fr>::new(1 << 4).unwrap();
        let size_as_fe = domain.size_as_field_element;
        let poly = DensePolynomial::rand(size, rng);

        let mut sum: Fr = Fr::zero();
        for eval in domain.elements().map(|e| poly.evaluate(e)) {
            sum += &eval;
        }
        let first = poly.coeffs[0] * size_as_fe;
        let last = *poly.coeffs.last().unwrap() * size_as_fe;
        println!("sum: {:?}", sum);
        println!("a_0: {:?}", first);
        println!("a_n: {:?}", last);
        println!("first + last: {:?}\n", first + last);
        assert_eq!(sum, first + last);
    }

    #[test]
    fn test_alternator_polynomial() {
        for i in 1..10 {
            for j in 1..i {
                let domain_i = EvaluationDomain::<Fr>::new(1 << i).unwrap();
                let domain_j = EvaluationDomain::<Fr>::new(1 << j).unwrap();
                let point = domain_j.sample_element_outside_domain(&mut snarkvm_utilities::test_rng());
                let j_elements = domain_j.elements().collect::<Vec<_>>();
                let slow_selector = {
                    let evals = domain_i
                        .elements()
                        .map(|e| if j_elements.contains(&e) { Fr::one() } else { Fr::zero() })
                        .collect();
                    Evaluations::from_vec_and_domain(evals, domain_i).interpolate()
                };
                assert_eq!(slow_selector.evaluate(point), domain_i.evaluate_selector_polynomial(domain_j, point));

                for element in domain_i.elements() {
                    if j_elements.contains(&element) {
                        assert_eq!(slow_selector.evaluate(element), Fr::one(), "failed for {} vs {}", i, j);
                    } else {
                        assert_eq!(slow_selector.evaluate(element), Fr::zero());
                    }
                }
            }
        }
    }
}
