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

use std::collections::BTreeMap;

use crate::{
    fft::DensePolynomial,
    polycommit::sonic_pc::{LabeledPolynomial, PolynomialInfo, PolynomialLabel},
    snark::marlin::{
        ahp::{verifier, AHPError, AHPForR1CS},
        prover,
        MarlinMode,
    },
};

use itertools::Itertools;
use rand_core::RngCore;
use rayon::prelude::*;
use snarkvm_fields::PrimeField;

impl<F: PrimeField, MM: MarlinMode> AHPForR1CS<F, MM> {
    /// Output the number of oracles sent by the prover in the third round.
    pub fn num_fourth_round_oracles() -> usize {
        1
    }

    /// Output the fourth round message and the next state.
    pub fn prover_fourth_round<R: RngCore>(
        verifier_message: verifier::ThirdMessage<F>,
        state: prover::State<'_, F, MM>,
        _r: &mut R,
    ) -> Result<prover::FourthOracles<F>, AHPError> {
        let lhs_sum: DensePolynomial<F> = verifier_message
            .into_iter()
            .zip_eq(state.lhs_polys_into_iter())
            .par_bridge()
            .map(|(delta, mut lhs)| {
                lhs *= delta;
                lhs
            })
            .reduce(
                || DensePolynomial::zero(),
                |mut a, mut b| {
                    a += &std::mem::take(&mut b);
                    a
                },
            );
        let h_2 = LabeledPolynomial::new("h_2".into(), lhs_sum, None, None);
        let oracles = prover::FourthOracles { h_2 };
        assert!(oracles.matches_info(&Self::fourth_round_polynomial_info()));
        Ok(oracles)
    }

    /// Output the degree bounds of oracles in the third round.
    pub fn fourth_round_polynomial_info() -> BTreeMap<PolynomialLabel, PolynomialInfo> {
        [("h_2".into(), PolynomialInfo::new("h_2".into(), None, None))].into()
    }
}
