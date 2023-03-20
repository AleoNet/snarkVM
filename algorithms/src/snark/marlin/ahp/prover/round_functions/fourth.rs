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
    polycommit::sonic_pc::{LabeledPolynomial, PolynomialInfo, PolynomialLabel},
    snark::marlin::{
        ahp::{verifier, AHPError, AHPForR1CS},
        prover,
        MarlinMode,
    }, fft::DensePolynomial,
};

use itertools::Itertools;
use rand_core::RngCore;
use snarkvm_fields::PrimeField;

impl<F: PrimeField, MM: MarlinMode> AHPForR1CS<F, MM> {
    /// Output the number of oracles sent by the prover in the third round.
    pub fn num_fourth_round_oracles() -> usize {
        1
    }
    
    /// Output the fourth round message and the next state.
    pub fn prover_fourth_round<'a, R: RngCore>(
        verifier_message: &verifier::ThirdMessage<F>,
        mut state: prover::State<'a, F, MM>,
        _r: &mut R,
    ) -> Result<prover::FourthOracles<F>, AHPError> {
        let verifier::ThirdMessage { r_a, r_b, r_c } = verifier_message;
        let mut lhs_s = state.circuit_specific_states.iter_mut().map(|(_,s)| s.lhs_polynomials.as_mut().unwrap()).collect_vec();
        let mut lhs_sum = DensePolynomial::zero();
        for i in 0..lhs_s.len() {
            let rs = [r_a[i], r_b[i], r_c[i]];
            for (lhs_s_i_j, r) in lhs_s[i].into_iter().zip(rs) {
                lhs_sum += &(std::mem::take(lhs_s_i_j)*r);
            }
        }
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
