// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{
    fft::{EvaluationDomain, Evaluations},
    polycommit::sonic_pc::{LabeledPolynomial, PolynomialInfo, PolynomialLabel},
    r1cs::{errors::SynthesisError, ConstraintSynthesizer, ConstraintSystem, LookupTable},
    snark::varuna::{
        ahp::{
            indexer::{Circuit, CircuitId, CircuitInfo, ConstraintSystem as IndexerConstraintSystem},
            matrices::arithmetize_matrix,
            AHPError,
            AHPForR1CS,
        },
        matrices::{matrix_evals, MatrixEvals},
        num_non_zero,
        witness_label,
        SNARKMode,
        TableInfo,
    },
};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::cfg_into_iter;

use anyhow::{anyhow, ensure, Result};
use core::marker::PhantomData;
use itertools::Itertools;
use std::collections::BTreeMap;

#[cfg(not(feature = "std"))]
use super::Matrix;
#[cfg(not(feature = "serial"))]
use rayon::prelude::*;

impl<F: PrimeField, MM: SNARKMode> AHPForR1CS<F, MM> {
    /// Output the number of oracles sent by the prover during indexing.
    pub fn num_indexing_oracles(num_circuits: usize, num_lookup_circuits: usize) -> usize {
        num_circuits * 12 + num_lookup_circuits * 5
    }

    /// Generate the index for this constraint system.
    pub fn index<C: ConstraintSynthesizer<F>>(c: &C) -> Result<Circuit<F, MM>> {
        let IndexerState {
            constraint_domain,
            variable_domain,

            a,
            non_zero_a_domain,
            a_evals,

            b,
            non_zero_b_domain,
            b_evals,

            c,
            non_zero_c_domain,
            c_evals,

            lookup_helper_state,

            index_info,
        } = Self::index_helper(c).map_err(|e| anyhow!("{e:?}"))?;
        let lookup_tables = lookup_helper_state.as_ref().map(|s| &s.lookup_tables);
        let s_mul_evals = lookup_helper_state.as_ref().map(|s| &s.s_mul_evals);
        let s_lookup_evals = lookup_helper_state.as_ref().map(|s| &s.s_lookup_evals);
        let id = Circuit::<F, MM>::hash(&index_info, &lookup_tables, &a, &b, &c, &s_mul_evals, &s_lookup_evals)?;
        let joint_arithmetization_time = start_timer!(|| format!("Arithmetizing A,B,C {id}"));

        let [a_arith, b_arith, c_arith]: [_; 3] = [("a", a_evals), ("b", b_evals), ("c", c_evals)]
            .into_iter()
            .map(|(label, evals)| arithmetize_matrix(&id, label, evals))
            .collect::<Result<Vec<_>, _>>()?
            .try_into()
            .unwrap();

        end_timer!(joint_arithmetization_time);

        let fft_precomp_time = start_timer!(|| format!("Precomputing roots of unity {id}"));

        let (fft_precomputation, ifft_precomputation) = Self::fft_precomputation(
            constraint_domain.size(),
            variable_domain.size(),
            non_zero_a_domain.size(),
            non_zero_b_domain.size(),
            non_zero_c_domain.size(),
        )
        .ok_or(anyhow!("The polynomial degree is too large"))?;
        end_timer!(fft_precomp_time);

        // TODO: consider abstracting lookup poly calculations into their own function
        let lookup_state = lookup_helper_state.is_some().then(|| {
            ensure!(
                lookup_helper_state.as_ref().unwrap().lookup_tables.iter().map(|t| t.table.len()).sum::<usize>()
                    <= constraint_domain.size(),
                "The number of lookup table entries must be less than or equal to the number of constraints"
            );
            let LookupHelperState { lookup_tables, s_mul_evals, s_lookup_evals, t_a_evals, t_b_evals, t_c_evals } =
                lookup_helper_state.unwrap();
            let lookup_poly_time = start_timer!(|| format!("Calculating lookup polys for {id}"));
            let s_mul_evals = Evaluations::from_vec_and_domain(s_mul_evals, constraint_domain);
            let s_mul = LabeledPolynomial::new(
                witness_label(id, "s_mul", 0),
                s_mul_evals.interpolate_with_pc_by_ref(&ifft_precomputation),
                None,
                None,
            );

            let s_lookup_evals_on_domain = Evaluations::from_vec_and_domain(s_lookup_evals.clone(), constraint_domain);
            let s_lookup = LabeledPolynomial::new(
                witness_label(id, "s_lookup", 0),
                s_lookup_evals_on_domain.interpolate_with_pc_by_ref(&ifft_precomputation),
                None,
                None,
            );

            let t_a_evals_on_domain = Evaluations::from_vec_and_domain(t_a_evals, constraint_domain);
            let t_a = LabeledPolynomial::new(
                format!("circuit_{id}_table_column_a"),
                t_a_evals_on_domain.interpolate_with_pc_by_ref(&ifft_precomputation),
                None,
                None,
            );
            let t_b_evals_on_domain = Evaluations::from_vec_and_domain(t_b_evals, constraint_domain);
            let t_b = LabeledPolynomial::new(
                format!("circuit_{id}_table_column_b"),
                t_b_evals_on_domain.interpolate_with_pc_by_ref(&ifft_precomputation),
                None,
                None,
            );
            let t_c_evals_on_domain = Evaluations::from_vec_and_domain(t_c_evals, constraint_domain);
            let t_c = LabeledPolynomial::new(
                format!("circuit_{id}_table_column_c"),
                t_c_evals_on_domain.interpolate_with_pc_by_ref(&ifft_precomputation),
                None,
                None,
            );

            let table_info = TableInfo { lookup_tables, t_a, t_b, t_c };
            end_timer!(lookup_poly_time);
            Ok(LookupState { s_mul, s_lookup, s_lookup_evals, table_info })
        });

        // A cleaner way would be to store lookup_state in Circuit, though that will be slightly more complicated to read further down the line
        let (table_info, s_mul, s_lookup, s_lookup_evals) = if let Some(lookup_state) = lookup_state {
            let LookupState { s_mul, s_lookup, s_lookup_evals, table_info } = lookup_state?;
            (Some(table_info), Some(s_mul), Some(s_lookup), Some(s_lookup_evals))
        } else {
            (None, None, None, None)
        };

        Ok(Circuit {
            index_info,
            table_info,
            a,
            b,
            c,
            a_arith,
            b_arith,
            c_arith,
            fft_precomputation,
            ifft_precomputation,
            s_mul,
            s_lookup,
            s_lookup_evals,
            id,
            _mode: PhantomData,
        })
    }

    pub fn index_polynomial_info<'a>(
        circuits: impl Iterator<Item = (&'a CircuitId, bool)> + 'a,
    ) -> BTreeMap<PolynomialLabel, PolynomialInfo> {
        let mut map = BTreeMap::new();
        for label in Self::index_polynomial_labels(["a", "b", "c"].into_iter(), circuits) {
            map.insert(label.clone(), PolynomialInfo::new(label, None, None));
        }
        map
    }

    // TODO: use witness_label for all of these
    pub fn index_polynomial_labels<'a>(
        matrices: impl Iterator<Item = &'a str> + Clone + 'a,
        circuits: impl Iterator<Item = (&'a CircuitId, bool)> + 'a,
    ) -> impl Iterator<Item = PolynomialLabel> + 'a {
        circuits.flat_map(move |(id, lookups_used)| {
            matrices.clone().flat_map(move |matrix| Self::index_polynomial_labels_m(*id, matrix)).chain(
                lookups_used
                    .then_some([
                        witness_label(*id, "s_mul", 0),
                        witness_label(*id, "s_lookup", 0),
                        format!("circuit_{id}_table_column_a"),
                        format!("circuit_{id}_table_column_b"),
                        format!("circuit_{id}_table_column_c"),
                    ])
                    .into_iter()
                    .flatten(),
            )
        })
    }

    pub fn index_polynomial_labels_m(id: CircuitId, matrix: &str) -> impl Iterator<Item = PolynomialLabel> {
        [
            format!("circuit_{id}_col_{matrix}"),
            format!("circuit_{id}_row_{matrix}"),
            format!("circuit_{id}_row_col_{matrix}"),
            format!("circuit_{id}_row_col_val_{matrix}"),
        ]
        .into_iter()
    }

    /// Generate indexed matrices, used by both the Prover and Verifier
    fn index_helper<C: ConstraintSynthesizer<F>>(c: &C) -> Result<IndexerState<F>, AHPError> {
        let index_time = start_timer!(|| "AHP::Index");

        let constraint_time = start_timer!(|| "Generating constraints");
        let mut ics = IndexerConstraintSystem::new();
        c.generate_constraints(&mut ics)?;
        end_timer!(constraint_time);

        let padding_time = start_timer!(|| "Padding matrices");
        // Given that we only use the matrix for indexing, the values we choose for assignments don't matter
        let random_assignments = None;
        MM::ZK.then(|| {
            crate::snark::varuna::ahp::matrices::add_randomizing_variables::<_, _>(&mut ics, random_assignments)
        });

        crate::snark::varuna::ahp::matrices::pad_input_for_indexer_and_prover(&mut ics);

        let a = ics.a_matrix();
        let b = ics.b_matrix();
        let c = ics.c_matrix();

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

        Self::num_formatted_public_inputs_is_admissible(num_padded_public_variables)?;

        let index_info = CircuitInfo {
            num_public_inputs: num_padded_public_variables,
            num_variables,
            num_constraints,
            num_non_zero_a,
            num_non_zero_b,
            num_non_zero_c,
        };

        let constraint_domain =
            EvaluationDomain::new(num_constraints).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let variable_domain = EvaluationDomain::new(num_variables).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let input_domain =
            EvaluationDomain::new(num_padded_public_variables).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let non_zero_a_domain =
            EvaluationDomain::new(num_non_zero_a).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let non_zero_b_domain =
            EvaluationDomain::new(num_non_zero_b).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let non_zero_c_domain =
            EvaluationDomain::new(num_non_zero_c).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let constraint_domain_elements = constraint_domain.elements().collect::<Vec<_>>();
        let variable_domain_elements = variable_domain.elements().collect::<Vec<_>>();

        let [a_evals, b_evals, c_evals]: [_; 3] =
            cfg_into_iter!([(&a, &non_zero_a_domain), (&b, &non_zero_b_domain), (&c, &non_zero_c_domain)])
                .map(|(matrix, non_zero_domain)| {
                    matrix_evals(
                        matrix,
                        non_zero_domain,
                        &variable_domain,
                        &input_domain,
                        &constraint_domain_elements,
                        &variable_domain_elements,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?
                .try_into()
                .unwrap();

        let lookups_used = !ics.lookup_constraints.is_empty();
        let lookup_helper_state = lookups_used.then(|| {
            let mut s_mul_evals = vec![F::zero(); num_constraints];
            ics.mul_constraints.iter().for_each(|index| s_mul_evals[*index] = F::one());

            let mut s_lookup_evals = vec![F::zero(); num_constraints];
            let mut lookup_tables = vec![];
            ics.lookup_constraints.iter().for_each(|entry| {
                lookup_tables.push(entry.table.clone());
                entry.indices.iter().for_each(|index| s_lookup_evals[*index] = F::one());
            });
            ics.mul_constraints.iter().for_each(|index| s_mul_evals[*index] = F::one());

            let (mut t_a_evals, mut t_b_evals, mut t_c_evals): (Vec<F>, Vec<F>, Vec<F>) = lookup_tables
                .iter()
                .flat_map(|table| table.table.iter().map(|(key, value)| (key[0], key[1], value)).collect_vec())
                .multiunzip();
            t_a_evals.resize(num_constraints, t_a_evals[0]);
            t_b_evals.resize(num_constraints, t_b_evals[0]);
            t_c_evals.resize(num_constraints, t_c_evals[0]);
            LookupHelperState { s_mul_evals, s_lookup_evals, lookup_tables, t_a_evals, t_b_evals, t_c_evals }
        });

        let result = Ok(IndexerState {
            constraint_domain,
            variable_domain,

            a,
            non_zero_a_domain,
            a_evals,

            b,
            non_zero_b_domain,
            b_evals,

            c,
            non_zero_c_domain,
            c_evals,

            lookup_helper_state,

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
        let lookups_used = state.lookup_helper_state.is_some();
        let labels = Self::index_polynomial_labels(["a", "b", "c"].into_iter(), std::iter::once((id, lookups_used)));
        let mut l_cache = BTreeMap::new();

        let lookup_evaluations = lookups_used.then(|| {
            let lookup_state = state.lookup_helper_state.unwrap();
            let R = state.constraint_domain;
            let R_l_coeffs =
                l_cache.entry((R.size(), point)).or_insert_with(|| R.evaluate_all_lagrange_coefficients(point));

            let s_mul_evals_on_domain = lookup_state.s_mul_evals;
            let s_mul = Evaluations::<F>::from_vec_and_domain(s_mul_evals_on_domain, R);
            let s_mul_at_point = s_mul.evaluate_with_coeffs(R_l_coeffs);

            let s_lookup_evals_on_domain = lookup_state.s_lookup_evals;
            let s_lookup = Evaluations::<F>::from_vec_and_domain(s_lookup_evals_on_domain, R);
            let s_lookup_at_point = s_lookup.evaluate_with_coeffs(R_l_coeffs);

            let t_a_evals_on_domain = lookup_state.t_a_evals;
            let t_a = Evaluations::<F>::from_vec_and_domain(t_a_evals_on_domain, R);
            let t_a_at_point = t_a.evaluate_with_coeffs(R_l_coeffs);

            let t_b_evals_on_domain = lookup_state.t_b_evals;
            let t_b = Evaluations::<F>::from_vec_and_domain(t_b_evals_on_domain, R);
            let t_b_at_point = t_b.evaluate_with_coeffs(R_l_coeffs);

            let t_c_evals_on_domain = lookup_state.t_c_evals;
            let t_c = Evaluations::<F>::from_vec_and_domain(t_c_evals_on_domain, R);
            let t_c_at_point = t_c.evaluate_with_coeffs(R_l_coeffs);
            [s_mul_at_point, s_lookup_at_point, t_a_at_point, t_b_at_point, t_c_at_point]
        });

        let index_evals = [
            (state.a_evals, state.non_zero_a_domain),
            (state.b_evals, state.non_zero_b_domain),
            (state.c_evals, state.non_zero_c_domain),
        ]
        .into_iter()
        .flat_map(|(evals, domain)| {
            let lagrange_coeffs_at_point = l_cache
                .entry((domain.size(), point))
                .or_insert_with(|| domain.evaluate_all_lagrange_coefficients(point));
            evals.evaluate(lagrange_coeffs_at_point).unwrap()
        })
        .chain(lookup_evaluations.into_iter().flatten());

        let evals = labels.zip_eq(index_evals).sorted_by(|(l1, _), (l2, _)| l1.cmp(l2));
        Ok(evals.map(|(_, eval)| eval))
    }
}

struct LookupState<F: PrimeField> {
    s_mul: LabeledPolynomial<F>,
    s_lookup: LabeledPolynomial<F>,
    s_lookup_evals: Vec<F>,
    table_info: TableInfo<F>,
}

struct LookupHelperState<F: PrimeField> {
    s_mul_evals: Vec<F>,
    s_lookup_evals: Vec<F>,
    lookup_tables: Vec<LookupTable<F>>,
    t_a_evals: Vec<F>,
    t_b_evals: Vec<F>,
    t_c_evals: Vec<F>,
}

struct IndexerState<F: PrimeField> {
    constraint_domain: EvaluationDomain<F>,
    variable_domain: EvaluationDomain<F>,

    a: Matrix<F>,
    non_zero_a_domain: EvaluationDomain<F>,
    a_evals: MatrixEvals<F>,

    b: Matrix<F>,
    non_zero_b_domain: EvaluationDomain<F>,
    b_evals: MatrixEvals<F>,

    c: Matrix<F>,
    non_zero_c_domain: EvaluationDomain<F>,
    c_evals: MatrixEvals<F>,

    lookup_helper_state: Option<LookupHelperState<F>>,

    index_info: CircuitInfo,
}
