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

use std::{collections::BTreeMap, sync::Arc};

use crate::{
    fft::Evaluations,
    polycommit::sonic_pc::{LabeledPolynomial, PolynomialInfo, PolynomialLabel},
    snark::marlin::{
        ahp::{AHPError, AHPForR1CS},
        prover,
        verifier,
        witness_label,
        MarlinMode,
    },
};
#[cfg(not(feature = "parallel"))]
use itertools::Itertools;
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{cfg_iter, cfg_iter_mut};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

impl<F: PrimeField, MM: MarlinMode> AHPForR1CS<F, MM> {
    /// Output the number of oracles sent by the prover in the second round.
    pub fn num_second_round_oracles(batch_size: usize) -> usize {
        6 * batch_size + 2
    }

    /// Output the degree bounds of oracles in the second round.
    pub fn second_round_polynomial_info(batch_size: usize) -> BTreeMap<PolynomialLabel, PolynomialInfo> {
        let mut polynomials = Vec::new();

        for i in 0..batch_size {
            polynomials.push(PolynomialInfo::new(witness_label("f", i), None, None));
            polynomials.push(PolynomialInfo::new(witness_label("s_1", i), None, None));
            polynomials.push(PolynomialInfo::new(witness_label("s_2", i), None, None));
            polynomials.push(PolynomialInfo::new(witness_label("z_2", i), None, None));
            polynomials.push(PolynomialInfo::new(witness_label("delta_omega_s_1", i), None, None));
            polynomials.push(PolynomialInfo::new(witness_label("omega_z_2", i), None, None));
        }
        polynomials.push(PolynomialInfo::new("table".to_string(), None, None));
        polynomials.push(PolynomialInfo::new("delta_table_omega".to_string(), None, None));
        polynomials.into_iter().map(|info| (info.label().into(), info)).collect()
    }

    /// Output the second round message and the next state.
    #[allow(clippy::type_complexity)]
    pub fn prover_second_round<'a>(
        verifier_message: &verifier::FirstMessage<F>,
        mut state: prover::State<'a, F, MM>,
    ) -> Result<prover::State<'a, F, MM>, AHPError> {
        let round_time = start_timer!(|| "AHP::Prover::SecondRound");
        let constraint_domain = state.constraint_domain;
        let batch_size = state.batch_size;

        let verifier::FirstMessage { zeta, delta, epsilon } = verifier_message;
        let zeta_squared = zeta.square();

        // Compute table and delta_table_omega poly
        let mut table_evals = state
            .index
            .lookup_tables
            .iter()
            .flat_map(|table| {
                table
                    .table
                    .iter()
                    .map(|(key, value)| key[0] + *zeta * key[1] + zeta_squared * value)
                    .collect::<Vec<F>>()
            })
            .collect::<Vec<F>>();
        // If the vector isn't empty we need to fill it with one of its elements.
        if !table_evals.is_empty() {
            table_evals.resize(state.index.index_info.num_constraints, table_evals[0]);
        } else {
            table_evals.resize(state.index.index_info.num_constraints, F::zero());
        }

        let table = LabeledPolynomial::new(
            "table".to_string(),
            Evaluations::from_vec_and_domain(table_evals.clone(), constraint_domain)
                .interpolate_with_pc_by_ref(state.ifft_precomputation()),
            None,
            None,
        );

        let mut delta_table_omega_evals = [&table_evals[1..], &[table_evals[0]]].concat();
        cfg_iter_mut!(delta_table_omega_evals).for_each(|e| *e *= delta);

        let delta_table_omega = LabeledPolynomial::new(
            "delta_table_omega".to_string(),
            Evaluations::from_vec_and_domain(delta_table_omega_evals.clone(), constraint_domain)
                .interpolate_with_pc_by_ref(state.ifft_precomputation()),
            None,
            None,
        );

        let z_a = state.z_a.take().unwrap();
        let z_b = state.z_b.take().unwrap();
        let z_c = state.z_c.take().unwrap();

        let batches = cfg_iter!(z_a)
            .enumerate()
            .zip_eq(z_b)
            .zip_eq(z_c)
            .map(|(((i, z_a), z_b), z_c)| {
                Self::calculate_table_polys(
                    witness_label("f", i),
                    witness_label("s_1", i),
                    witness_label("s_2", i),
                    witness_label("z_2", i),
                    witness_label("delta_omega_s_1", i),
                    witness_label("omega_z_2", i),
                    &table_evals,
                    &delta_table_omega_evals,
                    z_a,
                    &z_b,
                    &z_c,
                    &state.index.s_l_evals,
                    *zeta,
                    *delta,
                    *epsilon,
                    &state,
                )
            })
            .collect::<Vec<prover::SecondEntry<F>>>();

        assert_eq!(batches.len(), batch_size);

        let oracles = prover::SecondOracles { batches, table, delta_table_omega };
        assert!(oracles.matches_info(&Self::second_round_polynomial_info(batch_size)));
        state.verifier_first_message = Some(verifier_message.clone());
        state.second_round_oracles = Some(Arc::new(oracles));
        end_timer!(round_time);

        Ok(state)
    }

    #[allow(clippy::too_many_arguments)]
    fn calculate_table_polys<'a>(
        label_f: impl ToString,
        label_s_1: impl ToString,
        label_s_2: impl ToString,
        label_z_2: impl ToString,
        label_delta_s_1_omega: impl ToString,
        label_z_2_omega: impl ToString,
        table_evals: &[F],
        delta_table_omega_evals: &[F],
        z_a: &[F],
        z_b: &[F],
        z_c: &[F],
        s_l: &[F],
        zeta: F,
        delta: F,
        epsilon: F,
        state: &prover::State<'a, F, MM>,
    ) -> prover::SecondEntry<F> {
        let constraint_domain = state.constraint_domain;
        let zeta_squared = zeta.square();

        let f_evals = cfg_iter!(z_a)
            .zip(z_b)
            .zip(z_c)
            .zip(s_l)
            .map(
                |(((a, b), c), s)| {
                    if s.is_zero() { table_evals[table_evals.len() - 1] } else { *a + zeta * b + zeta_squared * c }
                },
            )
            .collect::<Vec<F>>();

        let f_poly = LabeledPolynomial::new(
            label_f.to_string(),
            Evaluations::from_vec_and_domain(f_evals.clone(), constraint_domain)
                .interpolate_with_pc_by_ref(state.ifft_precomputation()),
            None,
            None,
        );
        let mut s_evals = f_evals.clone();
        s_evals.extend(table_evals);
        // Split into alternating halves.
        let (s_1_evals, s_2_evals): (Vec<F>, Vec<F>) = s_evals.chunks(2).map(|els| (els[0], els[1])).unzip();
        let s_1_poly = LabeledPolynomial::new(
            label_s_1.to_string(),
            Evaluations::from_vec_and_domain(s_1_evals.clone(), constraint_domain)
                .interpolate_with_pc_by_ref(state.ifft_precomputation()),
            None,
            None,
        );
        let s_2_poly = LabeledPolynomial::new(
            label_s_2.to_string(),
            Evaluations::from_vec_and_domain(s_2_evals.clone(), constraint_domain)
                .interpolate_with_pc_by_ref(state.ifft_precomputation()),
            None,
            None,
        );

        let mut delta_s_1_omega_evals = [&s_1_evals[1..], &[s_1_evals[0]]].concat();
        cfg_iter_mut!(delta_s_1_omega_evals).for_each(|c| *c *= delta);

        // Calculate z_2
        // Compute divisions for each constraint
        let product_arguments = f_evals
            .iter()
            .zip(table_evals)
            .zip(&s_1_evals)
            .zip(&s_2_evals)
            .zip(delta_table_omega_evals)
            .zip(&delta_s_1_omega_evals)
            .take(f_evals.len() - 1)
            .map(|(((((f, t), s_1), s_2), d_t_omega), d_s_1_omega)| {
                let one_plus_delta = F::one() + delta;
                let epsilon_one_plus_delta = epsilon * one_plus_delta;
                one_plus_delta
                    * (epsilon + f)
                    * (epsilon_one_plus_delta + t + d_t_omega)
                    * ((epsilon_one_plus_delta + s_1 + delta * *s_2) * (epsilon_one_plus_delta + s_2 + d_s_1_omega))
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

        let z_2_poly = LabeledPolynomial::new(
            label_z_2.to_string(),
            Evaluations::from_vec_and_domain(z_2_evals.clone(), constraint_domain)
                .interpolate_with_pc_by_ref(state.ifft_precomputation()),
            None,
            None,
        );

        let delta_s_1_omega_poly = LabeledPolynomial::new(
            label_delta_s_1_omega.to_string(),
            Evaluations::from_vec_and_domain(delta_s_1_omega_evals.to_vec(), constraint_domain)
                .interpolate_with_pc_by_ref(state.ifft_precomputation()),
            None,
            None,
        );

        let z_2_omega_evals = &[&z_2_evals[1..], &[z_2_evals[0]]].concat();
        let z_2_omega_poly = LabeledPolynomial::new(
            label_z_2_omega.to_string(),
            Evaluations::from_vec_and_domain(z_2_omega_evals.to_vec(), constraint_domain)
                .interpolate_with_pc_by_ref(state.ifft_precomputation()),
            None,
            None,
        );

        prover::SecondEntry { f_poly, s_1_poly, s_2_poly, z_2_poly, delta_s_1_omega_poly, z_2_omega_poly }
    }
}
