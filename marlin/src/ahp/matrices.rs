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

#![allow(non_snake_case)]

use crate::{
    ahp::{indexer::Matrix, UnnormalizedBivariateLagrangePoly},
    BTreeMap,
};
use snarkvm_algorithms::fft::{EvaluationDomain, Evaluations as EvaluationsOnDomain};
use snarkvm_fields::{batch_inversion, Field, PrimeField};
use snarkvm_polycommit::LabeledPolynomial;
use snarkvm_r1cs::{ConstraintSystem, Index as VarIndex};
use snarkvm_utilities::{cfg_iter_mut, errors::SerializationError, serialize::*};

use derivative::Derivative;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

// This function converts a matrix output by Zexe's constraint infrastructure
// to the one used in this crate.
pub(crate) fn to_matrix_helper<F: Field>(matrix: &[Vec<(F, VarIndex)>], num_input_variables: usize) -> Matrix<F> {
    let mut new_matrix = Vec::with_capacity(matrix.len());
    for row in matrix {
        let mut new_row = Vec::with_capacity(row.len());
        for (fe, column) in row {
            let column = match column {
                VarIndex::Public(i) => *i,
                VarIndex::Private(i) => num_input_variables + i,
            };
            new_row.push((*fe, column))
        }
        new_matrix.push(new_row)
    }
    new_matrix
}

/// This must *always* be in sync with `make_matrices_square`.
pub(crate) fn padded_matrix_dim(num_formatted_variables: usize, num_constraints: usize) -> usize {
    core::cmp::max(num_formatted_variables, num_constraints)
}

/// Pads the public variables up to the closest power of two.
pub(crate) fn pad_input_for_indexer_and_prover<F: PrimeField, CS: ConstraintSystem<F>>(cs: &mut CS) {
    let num_public_variables = cs.num_public_variables();

    let power_of_two = EvaluationDomain::<F>::new(num_public_variables);
    assert!(power_of_two.is_some());

    // Allocated `zero` variables to pad the public input up to the next power of two.
    let padded_size = power_of_two.unwrap().size();
    if padded_size > num_public_variables {
        for i in 0..(padded_size - num_public_variables) {
            cs.alloc_input(|| format!("pad_input_{}", i), || Ok(F::zero())).unwrap();
        }
    }
}

pub(crate) fn make_matrices_square<F: Field, CS: ConstraintSystem<F>>(cs: &mut CS, num_formatted_variables: usize) {
    let num_constraints = cs.num_constraints();
    let matrix_padding = ((num_formatted_variables as isize) - (num_constraints as isize)).abs();

    if num_formatted_variables > num_constraints {
        use core::convert::identity as iden;
        // Add dummy constraints of the form 0 * 0 == 0
        for i in 0..matrix_padding {
            cs.enforce(|| format!("pad_constraint_{}", i), iden, iden, iden);
        }
    } else {
        // Add dummy unconstrained variables
        for i in 0..matrix_padding {
            let _ = cs
                .alloc(|| format!("pad_variable_{}", i), || Ok(F::one()))
                .expect("alloc failed");
        }
    }
}

#[derive(Derivative)]
#[derivative(Clone(bound = "F: PrimeField"))]
#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct MatrixEvals<F: PrimeField> {
    /// Evaluations of the `row` polynomial.
    pub row: EvaluationsOnDomain<F>,
    /// Evaluations of the `col` polynomial.
    pub col: EvaluationsOnDomain<F>,
    /// Evaluations of the `row_col` polynomial.
    pub row_col: EvaluationsOnDomain<F>,
    /// Evaluations of the `val_a` polynomial.
    pub val_a: EvaluationsOnDomain<F>,
    /// Evaluations of the `val_b` polynomial.
    pub val_b: EvaluationsOnDomain<F>,
    /// Evaluations of the `val_c` polynomial.
    pub val_c: EvaluationsOnDomain<F>,
}

/// Contains information about the arithmetization of the matrix M^*.
/// Here `M^*(i, j) := M(j, i) * u_H(j, j)`. For more details, see [\[COS20\]](https://eprint.iacr.org/2019/1076).
#[derive(Derivative)]
#[derivative(Clone(bound = "F: PrimeField"))]
#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct MatrixArithmetization<F: PrimeField> {
    /// LDE of the row indices of M^*.
    pub row: LabeledPolynomial<F>,
    /// LDE of the column indices of M^*.
    pub col: LabeledPolynomial<F>,
    /// LDE of the non-zero entries of A^*.
    pub val_a: LabeledPolynomial<F>,
    /// LDE of the non-zero entries of B^*.
    pub val_b: LabeledPolynomial<F>,
    /// LDE of the non-zero entries of C^*.
    pub val_c: LabeledPolynomial<F>,
    /// LDE of the vector containing entry-wise products of `row` and `col`,
    /// where `row` and `col` are as above.
    pub row_col: LabeledPolynomial<F>,

    /// Evaluation of `self.row`, `self.col`, and `self.val` on the domain `K`.
    pub evals_on_K: MatrixEvals<F>,
}

// TODO for debugging: add test that checks result of arithmetize_matrix(M).
pub(crate) fn arithmetize_matrix<F: PrimeField>(
    joint_matrix: &[Vec<usize>],
    a: &Matrix<F>,
    b: &Matrix<F>,
    c: &Matrix<F>,
    interpolation_domain: EvaluationDomain<F>,
    output_domain: EvaluationDomain<F>,
    input_domain: EvaluationDomain<F>,
) -> MatrixArithmetization<F> {
    let matrix_time = start_timer!(|| "Computing row, col, and val LDEs");

    let elems: Vec<_> = output_domain.elements().collect();

    let lde_evals_time = start_timer!(|| "Computing row, col and val evals");
    // Recall that we are computing the arithmetization of M^*,
    // where `M^*(i, j) := M(j, i) * u_H(j, j)`.
    let a = a
        .iter()
        .enumerate()
        .map(|(r, row)| row.iter().map(move |(f, i)| ((r, *i), *f)))
        .flatten()
        .collect::<BTreeMap<(usize, usize), F>>();

    let b = b
        .iter()
        .enumerate()
        .map(|(r, row)| row.iter().map(move |(f, i)| ((r, *i), *f)))
        .flatten()
        .collect::<BTreeMap<(usize, usize), F>>();

    let c = c
        .iter()
        .enumerate()
        .map(|(r, row)| row.iter().map(move |(f, i)| ((r, *i), *f)))
        .flatten()
        .collect::<BTreeMap<(usize, usize), F>>();

    let eq_poly_vals_time = start_timer!(|| "Precomputing eq_poly_vals");
    let eq_poly_vals: BTreeMap<F, F> = output_domain
        .elements()
        .zip(output_domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs())
        .collect();
    end_timer!(eq_poly_vals_time);

    let mut row_vec = Vec::with_capacity(interpolation_domain.size());
    let mut col_vec = Vec::with_capacity(interpolation_domain.size());
    let mut val_a_vec = Vec::with_capacity(interpolation_domain.size());
    let mut val_b_vec = Vec::with_capacity(interpolation_domain.size());
    let mut val_c_vec = Vec::with_capacity(interpolation_domain.size());
    let mut inverses = Vec::with_capacity(interpolation_domain.size());
    let mut count = 0;

    // Recall that we are computing the arithmetization of M^*,
    // where `M^*(i, j) := M(j, i) * u_H(j, j)`.
    for (r, row) in joint_matrix.into_iter().enumerate() {
        for i in row {
            let row_val = elems[r];
            let col_val = elems[output_domain.reindex_by_subdomain(input_domain, *i)];

            // We are dealing with the transpose of M
            row_vec.push(col_val);
            col_vec.push(row_val);
            // We insert zeros if a matrix doesn't contain an entry at the given (row, col) location.
            val_a_vec.push(a.get(&(r, *i)).copied().unwrap_or(F::zero()));
            val_b_vec.push(b.get(&(r, *i)).copied().unwrap_or(F::zero()));
            val_c_vec.push(c.get(&(r, *i)).copied().unwrap_or(F::zero()));
            inverses.push(eq_poly_vals[&col_val]);

            count += 1;
        }
    }
    batch_inversion::<F>(&mut inverses);
    drop(eq_poly_vals);

    cfg_iter_mut!(val_a_vec)
        .zip(&mut val_b_vec)
        .zip(&mut val_c_vec)
        .zip(inverses)
        .for_each(|(((v_a, v_b), v_c), inv)| {
            *v_a *= &inv;
            *v_b *= &inv;
            *v_c *= &inv;
        });
    end_timer!(lde_evals_time);

    for _ in count..interpolation_domain.size() {
        col_vec.push(elems[0]);
        row_vec.push(elems[0]);
        val_a_vec.push(F::zero());
        val_b_vec.push(F::zero());
        val_c_vec.push(F::zero());
    }

    let row_col_vec: Vec<_> = row_vec.iter().zip(&col_vec).map(|(row, col)| *row * col).collect();

    let interpolate_time = start_timer!(|| "Interpolating on K");
    let row_evals_on_K = EvaluationsOnDomain::from_vec_and_domain(row_vec, interpolation_domain);
    let col_evals_on_K = EvaluationsOnDomain::from_vec_and_domain(col_vec, interpolation_domain);
    let val_a_evals_on_K = EvaluationsOnDomain::from_vec_and_domain(val_a_vec, interpolation_domain);
    let val_b_evals_on_K = EvaluationsOnDomain::from_vec_and_domain(val_b_vec, interpolation_domain);
    let val_c_evals_on_K = EvaluationsOnDomain::from_vec_and_domain(val_c_vec, interpolation_domain);
    let row_col_evals_on_K = EvaluationsOnDomain::from_vec_and_domain(row_col_vec, interpolation_domain);

    let row = row_evals_on_K.clone().interpolate();
    let col = col_evals_on_K.clone().interpolate();
    let val_a = val_a_evals_on_K.clone().interpolate();
    let val_b = val_b_evals_on_K.clone().interpolate();
    let val_c = val_c_evals_on_K.clone().interpolate();
    let row_col = row_col_evals_on_K.clone().interpolate();

    end_timer!(interpolate_time);

    end_timer!(matrix_time);

    let evals_on_K = MatrixEvals {
        row: row_evals_on_K,
        col: col_evals_on_K,
        row_col: row_col_evals_on_K,
        val_a: val_a_evals_on_K,
        val_b: val_b_evals_on_K,
        val_c: val_c_evals_on_K,
    };

    MatrixArithmetization {
        row: LabeledPolynomial::new("row".into(), row, None, None),
        col: LabeledPolynomial::new("col".into(), col, None, None),
        val_a: LabeledPolynomial::new("a_val".into(), val_a, None, None),
        val_b: LabeledPolynomial::new("b_val".into(), val_b, None, None),
        val_c: LabeledPolynomial::new("c_val".into(), val_c, None, None),
        row_col: LabeledPolynomial::new("row_col".into(), row_col, None, None),
        evals_on_K,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::num_non_zero;
    use snarkvm_curves::bls12_377::Fr as F;
    use snarkvm_fields::{One, Zero};
    use snarkvm_utilities::{collections::BTreeMap, UniformRand};

    fn entry(matrix: &Matrix<F>, row: usize, col: usize) -> F {
        matrix[row]
            .iter()
            .find_map(|(f, i)| (i == &col).then(|| *f))
            .unwrap_or(F::zero())
    }

    #[test]
    fn check_arithmetization() {
        let a = vec![
            vec![(F::one(), 1), (F::one(), 2)],
            vec![(F::one(), 3)],
            vec![(F::one(), 3)],
            vec![(F::one(), 0), (F::one(), 1), (F::one(), 5)],
            vec![(F::one(), 1), (F::one(), 2), (F::one(), 6)],
            vec![(F::one(), 2), (F::one(), 5), (F::one(), 7)],
            vec![(F::one(), 3), (F::one(), 4), (F::one(), 6)],
            vec![(F::one(), 0), (F::one(), 6), (F::one(), 7)],
        ];

        let b = vec![
            vec![],
            vec![(F::one(), 1)],
            vec![(F::one(), 0)],
            vec![(F::one(), 2)],
            vec![(F::one(), 3)],
            vec![(F::one(), 4)],
            vec![(F::one(), 5)],
            vec![(F::one(), 6)],
        ];

        let c = vec![
            vec![],
            vec![(F::one(), 7)],
            vec![],
            vec![],
            vec![],
            vec![(F::one(), 3)],
            vec![],
            vec![],
        ];
        let joint_matrix = crate::ahp::indexer::sum_matrices(&a, &b, &c);
        let num_non_zero = num_non_zero(&joint_matrix);
        let interpolation_domain = EvaluationDomain::new(num_non_zero).unwrap();
        let output_domain = EvaluationDomain::new(2 + 6).unwrap();
        let input_domain = EvaluationDomain::new(2).unwrap();
        let joint_arith = arithmetize_matrix(
            &joint_matrix,
            &a,
            &b,
            &c,
            interpolation_domain,
            output_domain,
            input_domain,
        );
        let inverse_map = output_domain
            .elements()
            .enumerate()
            .map(|(i, e)| (e, i))
            .collect::<BTreeMap<_, _>>();
        let elements = output_domain.elements().collect::<Vec<_>>();
        let reindexed_inverse_map = (0..output_domain.size())
            .map(|i| {
                let reindexed_i = output_domain.reindex_by_subdomain(input_domain, i);
                (elements[reindexed_i], i)
            })
            .collect::<BTreeMap<_, _>>();

        let eq_poly_vals: BTreeMap<F, F> = output_domain
            .elements()
            .zip(output_domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs())
            .collect();

        let mut rng = snarkvm_utilities::test_rng();
        let eta_a = F::rand(&mut rng);
        let eta_b = F::rand(&mut rng);
        let eta_c = F::rand(&mut rng);
        for (k_index, k) in interpolation_domain.elements().enumerate() {
            let row_val = joint_arith.row.evaluate(k);
            let col_val = joint_arith.col.evaluate(k);

            let inverse = (eq_poly_vals[&row_val]).inverse().unwrap();
            // we're in transpose land.

            let val_a = joint_arith.val_a.evaluate(k);
            let val_b = joint_arith.val_b.evaluate(k);
            let val_c = joint_arith.val_c.evaluate(k);
            assert_eq!(joint_arith.evals_on_K.row[k_index], row_val);
            assert_eq!(joint_arith.evals_on_K.col[k_index], col_val);
            assert_eq!(joint_arith.evals_on_K.val_a[k_index], val_a);
            assert_eq!(joint_arith.evals_on_K.val_b[k_index], val_b);
            assert_eq!(joint_arith.evals_on_K.val_c[k_index], val_c);
            if k_index < num_non_zero {
                let col = *dbg!(reindexed_inverse_map.get(&row_val).unwrap());
                let row = *dbg!(inverse_map.get(&col_val).unwrap());
                assert!(joint_matrix[row].binary_search(&col).is_ok());
                assert_eq!(
                    eta_a * val_a + eta_b * val_b + eta_c * val_c,
                    inverse * (eta_a * entry(&a, row, col) + eta_b * entry(&b, row, col) + eta_c * entry(&c, row, col)),
                );
            }
        }
    }
}
