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

use std::collections::BTreeMap;

use crate::{
    fft::{DensePolynomial, Evaluations},
    polycommit::sonic_pc::{LabeledPolynomial, PolynomialInfo, PolynomialLabel},
    snark::marlin::{
        ahp::{indexer::CircuitInfo, verifier, AHPForR1CS},
        prover,
        MarlinMode,
    },
};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{cfg_iter, cfg_iter_mut};

#[cfg(not(feature = "parallel"))]
use itertools::Itertools;
use rand_core::RngCore;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

impl<F: PrimeField, MM: MarlinMode> AHPForR1CS<F, MM> {
    /// Output the number of oracles sent by the prover in the third round.
    pub fn num_third_round_oracles() -> usize {
        1
    }

    /// Output the degree bounds of oracles in the third round.
    pub fn third_round_polynomial_info(_info: &CircuitInfo<F>) -> BTreeMap<PolynomialLabel, PolynomialInfo> {
        [PolynomialInfo::new("h_1".into(), None, None)].into_iter().map(|info| (info.label().into(), info)).collect()
    }

    /// Output the third round message and the next state.
    pub fn prover_third_round<'a, R: RngCore>(
        verifier_message: &verifier::SecondMessage<F>,
        state: prover::State<'a, F, MM>,
        _r: &mut R,
    ) -> (prover::ThirdOracles<F>, prover::State<'a, F, MM>) {
        let constraint_domain = state.constraint_domain;

        let theta = verifier_message.theta;

        let verifier::FirstMessage { batch_combiners, .. } = state
            .verifier_first_message
            .as_ref()
            .expect("prover::State should include verifier_first_msg when prover_third_round is called");

        let zeta_squared = state.index.zeta.square();
        let one_plus_delta = F::one() + state.index.delta;
        let epsilon_one_plus_delta = state.index.epsilon * one_plus_delta;
        let l_1_evals = {
            let mut x_evals = vec![F::zero(); constraint_domain.size()];
            x_evals[0] = F::one();
            x_evals
        };

        let row = cfg_iter!(state.first_round_oracles.as_ref().unwrap().batches)
            .zip_eq(batch_combiners)
            .zip_eq(&state.plookup_evals)
            .map(|((b, combiner), evals)| {
                let lookup_poly = {
                    Evaluations::from_vec_and_domain(
                        evals[0]
                            .iter()
                            .zip(&evals[1])
                            .zip(&evals[2])
                            .zip(&evals[3])
                            .zip(&evals[4])
                            .zip(&evals[5])
                            .zip(&state.index.t_evals)
                            .zip(&state.index.delta_t_omega_evals)
                            .zip(&l_1_evals)
                            .take(state.index.index_info.num_constraints)
                            .map(|((((((((f, s_1), s_2), z_2), s_1_omega), z_2_omega), t), delta_t_omega), l_1)| {
                                let first = {
                                    let a = state.index.epsilon + f;
                                    let b = epsilon_one_plus_delta + t + delta_t_omega;
                                    *z_2 * one_plus_delta * a * b
                                };

                                let second = {
                                    let a = epsilon_one_plus_delta + s_1 + state.index.delta * s_2;
                                    let b = epsilon_one_plus_delta + s_2 + state.index.delta * s_1_omega;
                                    -(*z_2_omega) * a * b
                                };

                                let third = (*z_2 - F::one()) * *l_1;

                                first + second + third
                            })
                            .collect(),
                        constraint_domain,
                    )
                    .interpolate_with_pc_by_ref(state.ifft_precomputation())
                };

                let mut row_check = {
                    let z_a = b.z_a_poly.polynomial().as_dense().unwrap();
                    let mut z_b = b.z_b_poly.polynomial().as_dense().unwrap().clone();
                    let mut z_c = b.z_c_poly.polynomial().as_dense().unwrap().clone();
                    let f = b.f_poly.polynomial().as_dense().unwrap();
                    let mul_check = state.index.s_m.polynomial().as_dense().unwrap() * &(&(z_a * &z_b) - &z_c);
                    cfg_iter_mut!(z_b.coeffs).for_each(|b| *b *= state.index.zeta);
                    cfg_iter_mut!(z_c.coeffs).for_each(|c| *c *= zeta_squared);
                    let lookup_check =
                        state.index.s_l.polynomial().as_dense().unwrap() * &(&(&(z_a + &z_b) + &z_c) - f);

                    &(&mul_check + &lookup_check) + &lookup_poly
                };

                // Apply linear combination coefficient
                cfg_iter_mut!(row_check.coeffs).for_each(|c| *c *= combiner);
                row_check
            })
            .sum::<DensePolynomial<F>>();

        let mut h_1 = state.h_1.as_ref().unwrap().clone();
        cfg_iter_mut!(h_1.coeffs).for_each(|c| *c *= theta);

        let (div, rem) = row.divide_by_vanishing_poly(constraint_domain).unwrap();
        assert!(rem.is_zero());
        h_1 += &div;

        let oracles = prover::ThirdOracles { h_1: LabeledPolynomial::new("h_1".into(), h_1, None, None) };
        assert!(oracles.matches_info(&Self::third_round_polynomial_info(&state.index.index_info)));

        (oracles, state)
    }
}
