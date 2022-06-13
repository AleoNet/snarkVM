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

use core::convert::TryInto;
use std::collections::BTreeMap;

use crate::{
    fft,
    fft::{
        domain::IFFTPrecomputation,
        polynomial::PolyMultiplier,
        DensePolynomial,
        EvaluationDomain,
        SparsePolynomial,
    },
    polycommit::sonic_pc::{LabeledPolynomial, PolynomialInfo, PolynomialLabel},
    snark::marlin::{
        ahp::{
            indexer::{CircuitInfo, Matrix},
            verifier,
            AHPForR1CS,
            UnnormalizedBivariateLagrangePoly,
        },
        prover,
        MarlinMode,
    },
};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{cfg_iter, cfg_iter_mut, ExecutionPool};

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
    pub fn third_round_polynomial_info(info: &CircuitInfo<F>) -> BTreeMap<PolynomialLabel, PolynomialInfo> {
        [PolynomialInfo::new("h_1".into(), None, None)].into_iter().map(|info| (info.label().into(), info)).collect()
    }

    /// Output the third round message and the next state.
    pub fn prover_third_round<'a, R: RngCore>(
        verifier_message: &verifier::SecondMessage<F>,
        mut state: prover::State<'a, F, MM>,
        _r: &mut R,
    ) -> (prover::ThirdOracles<F>, prover::State<'a, F, MM>) {
        let constraint_domain = state.constraint_domain;

        let delta = verifier_message.delta;

        let verifier::FirstMessage { batch_combiners, .. } = state
            .verifier_first_message
            .as_ref()
            .expect("prover::State should include verifier_first_msg when prover_fourth_round is called");

        let zeta_squared = state.zeta.square();

        let row = cfg_iter!(state.first_round_oracles.as_ref().unwrap().batches)
            .zip_eq(batch_combiners)
            .map(|(b, combiner)| {
                let mut row_check = {
                    let z_a = b.z_a_poly.polynomial().as_dense().unwrap();
                    let mut z_b = b.z_b_poly.polynomial().as_dense().unwrap().clone();
                    let mut z_c = b.z_c_poly.polynomial().as_dense().unwrap().clone();
                    let f = b.f_poly.polynomial().as_dense().unwrap();
                    let s_m = b.s_m_poly.polynomial().as_dense().unwrap();
                    let s_l = b.s_l_poly.polynomial().as_dense().unwrap();
                    let mul_check = s_m * &(&(z_a * &z_b) - &z_c);
                    cfg_iter_mut!(z_b.coeffs).for_each(|b| *b *= state.zeta);
                    cfg_iter_mut!(z_c.coeffs).for_each(|c| *c *= zeta_squared);
                    let lookup_check = s_l * &(&(&(z_a + &z_b) + &z_c) - &f);
                    &mul_check + &lookup_check
                };

                // Apply linear combination coefficient
                cfg_iter_mut!(row_check.coeffs).for_each(|c| *c *= combiner);
                row_check
            })
            .sum::<DensePolynomial<F>>();

        let mut lin = state.lin.as_ref().unwrap().clone();
        cfg_iter_mut!(lin.coeffs).for_each(|c| *c *= delta);
        let mut x_g_1 = state.x_g_1.as_ref().unwrap().clone();
        cfg_iter_mut!(x_g_1.coeffs).for_each(|c| *c *= delta);

        let q_1 = &(&row + &lin) - &x_g_1;
        let (h_1, rem) = q_1.divide_by_vanishing_poly(constraint_domain).unwrap();
        // NOTE: maybe we need to check that rem is zero since there should be no remainer left

        let oracles = prover::ThirdOracles { h_1: LabeledPolynomial::new("h_1".into(), h_1, None, None) };
        assert!(oracles.matches_info(&Self::third_round_polynomial_info(&state.index.index_info)));

        (oracles, state)
    }
}
