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

use crate::{
    fft::EvaluationDomain,
    polycommit::sonic_pc::{PolynomialInfo, PolynomialLabel},
    snark::marlin::{
        ahp::{
            indexer::{Circuit, CircuitId, CircuitInfo, ConstraintSystem as IndexerConstraintSystem},
            matrices::arithmetize_matrix,
            AHPError,
            AHPForR1CS,
        },
        matrices::{matrix_evals, precomputation_for_matrix_evals, MatrixEvals},
        num_non_zero,
        MarlinMode,
    },
};
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSynthesizer, ConstraintSystem};
use snarkvm_utilities::cfg_into_iter;

use core::marker::PhantomData;
use std::collections::BTreeMap;

#[cfg(not(feature = "serial"))]
use rayon::prelude::*;
#[cfg(not(feature = "std"))]
use snarkvm_utilities::println;

use super::Matrix;

impl<F: PrimeField, MM: MarlinMode> AHPForR1CS<F, MM> {
    /// Generate the index for this constraint system.
    pub fn index<C: ConstraintSynthesizer<F>>(c: &C) -> Result<Circuit<F, MM>, AHPError> {
        let IndexerState {
            constraint_domain,

            a,
            non_zero_a_domain,
            a_evals,

            b,
            non_zero_b_domain,
            b_evals,

            c,
            non_zero_c_domain,
            c_evals,

            index_info,
        } = Self::index_helper(c)?;
        let id = Circuit::<F, MM>::hash(&index_info, &a, &b, &c).unwrap();
        let joint_arithmetization_time = start_timer!(|| format!("Arithmetizing A,B,C {id}"));
        let [a_arith, b_arith, c_arith]: [_; 3] = [("a", a_evals), ("b", b_evals), ("c", c_evals)]
            .into_iter()
            .map(|(label, evals)| arithmetize_matrix(&id, label, evals))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        end_timer!(joint_arithmetization_time);

        let fft_precomp_time = start_timer!(|| format!("Precomputing roots of unity {id}"));

        let (fft_precomputation, ifft_precomputation) = Self::fft_precomputation(
            constraint_domain.size(),
            non_zero_a_domain.size(),
            non_zero_b_domain.size(),
            non_zero_c_domain.size(),
        )
        .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        end_timer!(fft_precomp_time);

        Ok(Circuit {
            index_info,
            a,
            b,
            c,
            a_arith,
            b_arith,
            c_arith,
            fft_precomputation,
            ifft_precomputation,
            id,
            _mode: PhantomData,
        })
    }

    pub fn index_polynomial_info<'a>(
        circuit_ids: impl Iterator<Item = &'a CircuitId> + 'a,
    ) -> BTreeMap<PolynomialLabel, PolynomialInfo> {
        let mut map = BTreeMap::new();
        for label in Self::index_polynomial_labels(&["a", "b", "c"], circuit_ids) {
            map.insert(label.clone(), PolynomialInfo::new(label, None, None));
        }
        map
    }

    pub fn index_polynomial_labels<'a>(
        matrices: &'a [&str],
        ids: impl Iterator<Item = &'a CircuitId> + 'a,
    ) -> impl Iterator<Item = PolynomialLabel> + 'a {
        ids.flat_map(move |id| {
            matrices.iter().flat_map(move |matrix| {
                [
                    format!("circuit_{id}_row_{matrix}"),
                    format!("circuit_{id}_col_{matrix}"),
                    format!("circuit_{id}_val_{matrix}"),
                    format!("circuit_{id}_row_col_{matrix}"),
                ]
            })
        })
    }

    fn index_helper<C: ConstraintSynthesizer<F>>(c: &C) -> Result<IndexerState<F>, AHPError> {
        let index_time = start_timer!(|| "AHP::Index");

        let constraint_time = start_timer!(|| "Generating constraints");
        let mut ics = IndexerConstraintSystem::new();
        c.generate_constraints(&mut ics)?;
        end_timer!(constraint_time);

        let padding_time = start_timer!(|| "Padding matrices to make them square");
        crate::snark::marlin::ahp::matrices::pad_input_for_indexer_and_prover(&mut ics);
        ics.make_matrices_square();

        let a = ics.a_matrix();
        let b = ics.b_matrix();
        let c = ics.c_matrix();

        // balance_matrices(&mut a, &mut b);
        end_timer!(padding_time);

        let num_padded_public_variables = ics.num_public_variables();
        let num_private_variables = ics.num_private_variables();
        let num_constraints = ics.num_constraints();
        let num_non_zero_a = num_non_zero(&a);
        let num_non_zero_b = num_non_zero(&b);
        let num_non_zero_c = num_non_zero(&c);
        let num_variables = num_padded_public_variables + num_private_variables;

        if cfg!(debug_assertions) {
            println!("Number of padded public variables: {num_padded_public_variables}");
            println!("Number of private variables: {num_private_variables}");
            println!("Number of num_constraints: {num_constraints}");
            println!("Number of non-zero entries in A: {num_non_zero_a}");
            println!("Number of non-zero entries in B: {num_non_zero_b}");
            println!("Number of non-zero entries in C: {num_non_zero_c}");
        }

        if num_constraints != num_variables {
            eprintln!("Number of padded public variables: {num_padded_public_variables}");
            eprintln!("Number of private variables: {num_private_variables}");
            eprintln!("Number of num_constraints: {num_constraints}");
            eprintln!("Number of non-zero entries in A: {num_non_zero_a}");
            eprintln!("Number of non-zero entries in B: {num_non_zero_b}");
            eprintln!("Number of non-zero entries in C: {num_non_zero_c}");
            return Err(AHPError::NonSquareMatrix);
        }

        Self::num_formatted_public_inputs_is_admissible(num_padded_public_variables)?;

        let index_info = CircuitInfo {
            num_public_inputs: num_padded_public_variables,
            num_variables,
            num_constraints,
            num_non_zero_a,
            num_non_zero_b,
            num_non_zero_c,
            f: PhantomData,
        };

        let constraint_domain =
            EvaluationDomain::new(num_constraints).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let input_domain =
            EvaluationDomain::new(num_padded_public_variables).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let non_zero_a_domain =
            EvaluationDomain::new(num_non_zero_a).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let non_zero_b_domain =
            EvaluationDomain::new(num_non_zero_b).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let non_zero_c_domain =
            EvaluationDomain::new(num_non_zero_c).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let (constraint_domain_elements, constraint_domain_eq_poly_vals) =
            precomputation_for_matrix_evals(&constraint_domain);

        let [a_evals, b_evals, c_evals]: [_; 3] =
            cfg_into_iter!([(&a, &non_zero_a_domain), (&b, &non_zero_b_domain), (&c, &non_zero_c_domain),])
                .map(|(matrix, non_zero_domain)| {
                    matrix_evals(
                        matrix,
                        non_zero_domain,
                        &constraint_domain,
                        &input_domain,
                        &constraint_domain_elements,
                        &constraint_domain_eq_poly_vals,
                    )
                })
                .collect::<Vec<_>>()
                .try_into()
                .unwrap();

        let result = Ok(IndexerState {
            constraint_domain,

            a,
            non_zero_a_domain,
            a_evals,

            b,
            non_zero_b_domain,
            b_evals,

            c,
            non_zero_c_domain,
            c_evals,

            index_info,
        });
        end_timer!(index_time);
        result
    }

    pub fn evaluate_index_polynomials<C: ConstraintSynthesizer<F>>(
        c: &C,
        id: &CircuitId,
        point: F,
    ) -> Result<impl Iterator<Item = F>, AHPError> {
        let state = Self::index_helper(c)?;
        let mut evals = [
            (state.a_evals, state.non_zero_a_domain),
            (state.b_evals, state.non_zero_b_domain),
            (state.c_evals, state.non_zero_c_domain),
        ]
        .into_iter()
        .flat_map(move |(evals, domain)| {
            let labels = Self::index_polynomial_labels(&["a", "b", "c"], std::iter::once(id));
            let lagrange_coefficients_at_point = domain.evaluate_all_lagrange_coefficients(point);
            labels.zip(evals.evaluate(&lagrange_coefficients_at_point))
        })
        .collect::<Vec<_>>();
        evals.sort_by(|(l1, _), (l2, _)| l1.cmp(l2));
        Ok(evals.into_iter().map(|(_, eval)| eval))
    }
}

struct IndexerState<F: PrimeField> {
    constraint_domain: EvaluationDomain<F>,

    a: Matrix<F>,
    non_zero_a_domain: EvaluationDomain<F>,
    a_evals: MatrixEvals<F>,

    b: Matrix<F>,
    non_zero_b_domain: EvaluationDomain<F>,
    b_evals: MatrixEvals<F>,

    c: Matrix<F>,
    non_zero_c_domain: EvaluationDomain<F>,
    c_evals: MatrixEvals<F>,

    index_info: CircuitInfo<F>,
}
