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

use crate::{
    ahp::{matrices, prover::ProverConstraintSystem, verifier, AHPError, CircuitInfo},
    marlin::MarlinMode,
    prover::ProverMessage,
    String,
    ToString,
    Vec,
};
use snarkvm_algorithms::fft::{EvaluationDomain, SparsePolynomial};
use snarkvm_fields::{Field, PrimeField};
use snarkvm_r1cs::errors::SynthesisError;

use snarkvm_polycommit::{LCTerm, LabeledPolynomial, LinearCombination};

use core::{borrow::Borrow, marker::PhantomData};

/// The algebraic holographic proof defined in [CHMMVW19](https://eprint.iacr.org/2019/1047).
/// Currently, this AHP only supports inputs of size one
/// less than a power of 2 (i.e., of the form 2^n - 1).
pub struct AHPForR1CS<F: Field, MM: MarlinMode> {
    field: PhantomData<F>,
    mode: PhantomData<MM>,
}

impl<F: PrimeField, MM: MarlinMode> AHPForR1CS<F, MM> {
    /// The labels for the polynomials output by the AHP indexer.
    #[rustfmt::skip]
    pub const INDEXER_POLYNOMIALS: [&'static str; 12] = [
        // Polynomials for M
        "row_a", "col_a", "val_a", "row_col_a",
        "row_b", "col_b", "val_b", "row_col_b",
        "row_c", "col_c", "val_c", "row_col_c",
    ];
    /// The labels for the polynomials output and vanishing polynomials by the AHP indexer.
    #[rustfmt::skip]
    pub const INDEXER_POLYNOMIALS_WITH_VANISHING: [&'static str; 14] = [
        // Polynomials for M
        "row_a", "col_a", "val_a", "row_col_a",
        "row_b", "col_b", "val_b", "row_col_b",
        "row_c", "col_c", "val_c", "row_col_c",
        // Vanishing polynomials
        "vanishing_poly_h", "vanishing_poly_k"
    ];
    /// The linear combinations that are statically known to evaluate to zero.
    #[rustfmt::skip]
    pub const LC_WITH_ZERO_EVAL: [&'static str; 2] = ["inner_sumcheck", "outer_sumcheck"];
    /// The labels for the polynomials output by the AHP prover.
    #[rustfmt::skip]
    pub const PROVER_POLYNOMIALS_WITHOUT_ZK: [&'static str; 9] = [
        // First sumcheck
        "w", "z_a", "z_b", "g_1", "h_1",
        // Second sumcheck
        "g_a", "g_b", "g_c", "h_2",
    ];
    /// The labels for the polynomials output by the AHP prover.
    #[rustfmt::skip]
    pub const PROVER_POLYNOMIALS_WITH_ZK: [&'static str; 10] = [
        // First sumcheck
        "w", "z_a", "z_b", "mask_poly", "g_1", "h_1",
        // Second sumcheck
        "g_a", "g_b", "g_c", "h_2",
    ];

    pub(crate) fn indexer_polynomials() -> impl Iterator<Item = &'static str> {
        if MM::RECURSION {
            Self::INDEXER_POLYNOMIALS_WITH_VANISHING.as_ref().iter().copied()
        } else {
            Self::INDEXER_POLYNOMIALS.as_ref().iter().copied()
        }
    }

    pub(crate) fn prover_polynomials() -> impl Iterator<Item = &'static str> {
        if MM::ZK {
            Self::PROVER_POLYNOMIALS_WITH_ZK.as_ref().iter().copied()
        } else {
            Self::PROVER_POLYNOMIALS_WITHOUT_ZK.as_ref().iter().copied()
        }
    }

    pub(crate) fn polynomial_labels() -> impl Iterator<Item = String> {
        Self::indexer_polynomials()
            .chain(Self::prover_polynomials())
            .map(|s| s.to_string())
    }

    /// Check that the (formatted) public input is of the form 2^n for some integer n.
    pub fn num_formatted_public_inputs_is_admissible(num_inputs: usize) -> bool {
        num_inputs.count_ones() == 1
    }

    /// Check that the (formatted) public input is of the form 2^n for some integer n.
    pub fn formatted_public_input_is_admissible(input: &[F]) -> bool {
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
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let non_zero_domain_size = EvaluationDomain::<F>::compute_size_of_domain(num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        Ok(*[
            2 * constraint_domain_size + zk_bound - 2,
            if MM::ZK {
                3 * constraint_domain_size + 2 * zk_bound - 3
            } else {
                0
            }, //  mask_poly
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
        let mut degree_bounds = [0usize; 2];
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
        [domain_a, domain_b, domain_c]
            .into_iter()
            .max_by_key(|d| d.size())
            .unwrap()
    }

    /// Construct the linear combinations that are checked by the AHP.
    /// Public input should be unformatted.
    #[allow(non_snake_case)]
    pub fn construct_linear_combinations<E: EvaluationsProvider<F>>(
        public_input: &[F],
        evals: &E,
        prover_third_message: &ProverMessage<F>,
        state: &verifier::VerifierState<F, MM>,
    ) -> Result<Vec<LinearCombination<F>>, AHPError> {
        let constraint_domain = state.constraint_domain;
        let non_zero_a_domain = state.non_zero_a_domain;
        let non_zero_b_domain = state.non_zero_b_domain;
        let non_zero_c_domain = state.non_zero_c_domain;
        let largest_non_zero_domain = Self::max_non_zero_domain_helper(
            state.non_zero_a_domain,
            state.non_zero_b_domain,
            state.non_zero_c_domain,
        );

        let public_input = ProverConstraintSystem::format_public_input(public_input);
        if !Self::formatted_public_input_is_admissible(&public_input) {
            return Err(AHPError::InvalidPublicInputLength);
        }
        let input_domain = EvaluationDomain::new(public_input.len()).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let first_round_msg = state.first_round_message.unwrap();
        let alpha = first_round_msg.alpha;
        let eta_a = F::one();
        let eta_b = first_round_msg.eta_b;
        let eta_c = first_round_msg.eta_c;

        let a_at_beta = prover_third_message.field_elements[0];
        let b_at_beta = prover_third_message.field_elements[1];
        let c_at_beta = prover_third_message.field_elements[2];
        let t_at_beta = a_at_beta + b_at_beta + c_at_beta;

        let beta = state.second_round_message.unwrap().beta;
        let gamma = state.gamma.unwrap();

        let mut linear_combinations = Vec::with_capacity(9);

        // Outer sumchecK:
        let z_b = LinearCombination::new("z_b", vec![(F::one(), "z_b")]);
        let g_1 = LinearCombination::new("g_1", vec![(F::one(), "g_1")]);

        let r_alpha_at_beta = constraint_domain.eval_unnormalized_bivariate_lagrange_poly(alpha, beta);
        let v_H_at_alpha = constraint_domain.evaluate_vanishing_polynomial(alpha);
        let v_H_at_beta = constraint_domain.evaluate_vanishing_polynomial(beta);
        let v_X_at_beta = input_domain.evaluate_vanishing_polynomial(beta);

        let z_b_at_beta = evals.get_lc_eval(&z_b, beta)?;
        let g_1_at_beta = evals.get_lc_eval(&g_1, beta)?;

        let x_at_beta = input_domain
            .evaluate_all_lagrange_coefficients(beta)
            .into_iter()
            .zip(public_input)
            .map(|(l, x)| l * x)
            .fold(F::zero(), |x, y| x + y);

        #[rustfmt::skip]
        let outer_sumcheck = {
            let mut lc_terms = vec![];
            if MM::ZK {
                lc_terms.push((F::one(), "mask_poly".into()));
            }
            lc_terms.push((r_alpha_at_beta * (eta_a + (eta_c * z_b_at_beta)), "z_a".into()));
            lc_terms.push((r_alpha_at_beta * eta_b * z_b_at_beta, LCTerm::One));
            lc_terms.push((-t_at_beta * v_X_at_beta, "w".into()));
            lc_terms.push((-t_at_beta * x_at_beta, LCTerm::One));
            lc_terms.push((-v_H_at_beta, "h_1".into()));
            lc_terms.push((-beta * g_1_at_beta, LCTerm::One));
            LinearCombination::new("outer_sumcheck", lc_terms)
        };
        debug_assert!(evals.get_lc_eval(&outer_sumcheck, beta)?.is_zero());

        linear_combinations.push(z_b);
        linear_combinations.push(g_1);
        linear_combinations.push(outer_sumcheck);

        //  Inner sumcheck:
        let mut inner_sumcheck = LinearCombination::empty("inner_sumcheck");

        let beta_alpha = beta * alpha;

        let g_a = LinearCombination::new("g_a", vec![(F::one(), "g_a")]);
        let g_a_at_gamma = evals.get_lc_eval(&g_a, gamma)?;
        let v_K_a_at_gamma = non_zero_a_domain.evaluate_vanishing_polynomial(gamma);
        let selector_a = largest_non_zero_domain
            .selector_polynomial(non_zero_a_domain)
            .evaluate(gamma);
        let lhs_a = Self::construct_lhs(
            "a",
            eta_a,
            alpha,
            beta,
            gamma,
            v_H_at_alpha * v_H_at_beta,
            g_a_at_gamma,
            a_at_beta,
            non_zero_a_domain.size_as_field_element,
            selector_a,
        );
        inner_sumcheck += &lhs_a;

        let g_b = LinearCombination::new("g_b", vec![(F::one(), "g_b")]);
        let g_b_at_gamma = evals.get_lc_eval(&g_b, gamma)?;
        let v_K_b_at_gamma = non_zero_b_domain.evaluate_vanishing_polynomial(gamma);
        let selector_b = largest_non_zero_domain
            .selector_polynomial(non_zero_b_domain)
            .evaluate(gamma);
        let lhs_b = Self::construct_lhs(
            "b",
            eta_b,
            alpha,
            beta,
            gamma,
            v_H_at_alpha * v_H_at_beta,
            g_b_at_gamma,
            b_at_beta,
            non_zero_b_domain.size_as_field_element,
            selector_b,
        );
        inner_sumcheck += &lhs_b;

        let g_c = LinearCombination::new("g_c", vec![(F::one(), "g_c")]);
        let g_c_at_gamma = evals.get_lc_eval(&g_c, gamma)?;
        let v_K_c_at_gamma = non_zero_c_domain.evaluate_vanishing_polynomial(gamma);
        let selector_c = largest_non_zero_domain
            .selector_polynomial(non_zero_c_domain)
            .evaluate(gamma);
        let lhs_c = Self::construct_lhs(
            "c",
            eta_c,
            alpha,
            beta,
            gamma,
            v_H_at_alpha * v_H_at_beta,
            g_c_at_gamma,
            c_at_beta,
            non_zero_c_domain.size_as_field_element,
            selector_c,
        );
        inner_sumcheck += &lhs_c;

        inner_sumcheck -= &LinearCombination::new("h_2", vec![(
            largest_non_zero_domain.evaluate_vanishing_polynomial(gamma),
            "h_2",
        )]);
        debug_assert!(evals.get_lc_eval(&inner_sumcheck, gamma)?.is_zero());

        linear_combinations.push(g_a);
        linear_combinations.push(g_b);
        linear_combinations.push(g_c);
        linear_combinations.push(inner_sumcheck);

        if MM::RECURSION {
            let vanishing_poly_h_alpha =
                LinearCombination::new("vanishing_poly_h_alpha", vec![(F::one(), "vanishing_poly_h")]);
            let vanishing_poly_h_beta =
                LinearCombination::new("vanishing_poly_h_beta", vec![(F::one(), "vanishing_poly_h")]);
            let vanishing_poly_k_gamma =
                LinearCombination::new("vanishing_poly_k_gamma", vec![(F::one(), "vanishing_poly_k")]);

            linear_combinations.push(vanishing_poly_h_alpha);
            linear_combinations.push(vanishing_poly_h_beta);
            linear_combinations.push(vanishing_poly_k_gamma);
        }

        linear_combinations.sort_by(|a, b| a.label.cmp(&b.label));
        Ok(linear_combinations)
    }

    fn construct_lhs(
        label: &str,
        eta: F,
        alpha: F,
        beta: F,
        gamma: F,
        v_h_at_alpha_beta: F,
        g_at_gamma: F,
        sum: F,
        k_size: F,
        selector_at_gamma: F,
    ) -> LinearCombination<F> {
        let a = LinearCombination::new("a_poly".to_owned() + label, vec![(
            eta * v_h_at_alpha_beta,
            "val".to_owned() + label,
        )]);
        let alpha_beta = alpha * beta;

        let b = LinearCombination::new("denom".to_owned() + label, vec![
            (alpha_beta, LCTerm::One),
            (-alpha, ("row".to_owned() + label).into()),
            (-beta, ("col".to_owned() + label).into()),
            (F::one(), ("row_col".to_owned() + label).into()),
        ]);
        b *= gamma * g_at_gamma + (sum / k_size);

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
pub trait EvaluationsProvider<F: Field> {
    /// Get the evaluation of linear combination `lc` at `point`.
    fn get_lc_eval(&self, lc: &LinearCombination<F>, point: F) -> Result<F, AHPError>;
}

impl<'a, F: Field> EvaluationsProvider<F> for snarkvm_polycommit::Evaluations<'a, F> {
    fn get_lc_eval(&self, lc: &LinearCombination<F>, point: F) -> Result<F, AHPError> {
        let key = (lc.label.clone(), point);
        self.get(&key)
            .copied()
            .ok_or_else(|| AHPError::MissingEval(lc.label.clone()))
    }
}

impl<F: Field, T: Borrow<LabeledPolynomial<F>>> EvaluationsProvider<F> for Vec<T> {
    fn get_lc_eval(&self, lc: &LinearCombination<F>, point: F) -> Result<F, AHPError> {
        let mut eval = F::zero();
        for (coeff, term) in lc.iter() {
            let value = if let LCTerm::PolyLabel(label) = term {
                self.iter()
                    .find(|p| {
                        let p: &LabeledPolynomial<F> = (*p).borrow();
                        p.label() == label
                    })
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

    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(&self, x: F) -> Vec<F> {
        let vanish_x = self.evaluate_vanishing_polynomial(x);
        let mut inverses: Vec<F> = self.elements().map(|y| x - y).collect();
        snarkvm_fields::batch_inversion_and_mul(&mut inverses, &vanish_x);
        inverses
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
    fn selector_polynomial(&self, other: EvaluationDomain<F>) -> SparsePolynomial<F>;
}

impl<F: PrimeField> SelectorPolynomial<F> for EvaluationDomain<F> {
    fn selector_polynomial(&self, other: EvaluationDomain<F>) -> SparsePolynomial<F> {
        assert!(self.size() >= other.size());
        let coeff = self.size_as_field_element / other.size_as_field_element;
        SparsePolynomial::from_coefficients_vec(vec![(0, coeff), (self.size(), coeff)])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_algorithms::fft::{DensePolynomial, Evaluations};
    use snarkvm_curves::bls12_377::fr::Fr;
    use snarkvm_fields::{One, Zero};
    use snarkvm_utilities::rand::{test_rng, UniformRand};

    #[test]
    fn domain_unnormalized_bivariate_lagrange_poly() {
        for domain_size in 1..10 {
            let domain = EvaluationDomain::<Fr>::new(1 << domain_size).unwrap();
            let manual: Vec<_> = domain
                .elements()
                .map(|elem| domain.eval_unnormalized_bivariate_lagrange_poly(elem, elem))
                .collect();
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
            let manual: Vec<_> = domain
                .elements()
                .map(|y| domain.eval_unnormalized_bivariate_lagrange_poly(x, y))
                .collect();
            let fast = domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(x);
            assert_eq!(fast, manual);
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
                let selector = domain_i.selector_polynomial(domain_j);
                let j_elements = domain_j.elements().collect::<Vec<_>>();
                let slow_selector = {
                    let evals = domain_i
                        .elements()
                        .map(|e| if j_elements.contains(&e) { Fr::one() } else { Fr::zero() })
                        .collect();
                    Evaluations::from_vec_and_domain(evals, domain_i).interpolate()
                };
                assert_eq!(DensePolynomial::from(selector.clone()), slow_selector);

                for element in domain_i.elements() {
                    if j_elements.contains(&element) {
                        assert_eq!(selector.evaluate(element), Fr::one(), "failed for {} vs {}", i, j);
                    } else {
                        assert_eq!(selector.evaluate(element), Fr::zero());
                    }
                }
            }
        }
    }
}
