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
    fft::DensePolynomial,
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
        let row = cfg_iter!(state.first_round_oracles.as_ref().unwrap().batches)
            .zip_eq(batch_combiners)
            .map(|(b, combiner)| {
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

                    &mul_check + &lookup_check
                };

                let lookup_poly = {
                    let mut f = b.f_poly.polynomial().as_dense().unwrap().clone();
                    let mut s_1 = b.s_1_poly.polynomial().as_dense().unwrap().clone();
                    let mut s_2 = b.s_2_poly.polynomial().as_dense().unwrap().clone();
                    let mut z_2 = b.z_2_poly.polynomial().as_dense().unwrap().clone();
                    let s_1_omega = b.s_1_omega_poly.polynomial().as_dense().unwrap();
                    let z_2_omega = b.z_2_omega_poly.polynomial().as_dense().unwrap();
                    let mut t = state.index.t.polynomial().as_dense().unwrap().clone();
                    let delta_t_omega = state.index.delta_t_omega.polynomial().as_dense().unwrap();
                    let l_1 = state.index.l_1.polynomial().as_dense().unwrap();
                    let first = {
                        if f.degree() > 0 {
                            f.coeffs[0] += state.index.epsilon;
                        } else {
                            f.coeffs.push(state.index.epsilon);
                        }

                        if t.degree() > 0 {
                            t.coeffs[0] += epsilon_one_plus_delta;
                        } else {
                            t.coeffs.push(epsilon_one_plus_delta);
                        }

                        let a = &t + delta_t_omega;
                        &(&z_2.clone() * &(f * one_plus_delta)) * &a
                    };

                    let second = {
                        if s_1.degree() > 0 {
                            s_1.coeffs[0] += epsilon_one_plus_delta;
                        } else {
                            s_1.coeffs.push(epsilon_one_plus_delta);
                        }
                        let a = &s_1 + &(s_2.clone() * state.index.delta);
                        if s_2.degree() > 0 {
                            s_2.coeffs[0] += epsilon_one_plus_delta;
                        } else {
                            s_2.coeffs.push(epsilon_one_plus_delta);
                        }
                        let b = &s_2 + &(s_1_omega * state.index.delta);
                        &(&(z_2_omega * -F::one()) * &a) * &b
                    };

                    z_2.coeffs[0] -= F::one();
                    let third = &z_2 * l_1;

                    &(&first + &second) + &third
                };

                row_check += &lookup_poly;

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
