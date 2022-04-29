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

use core::marker::PhantomData;

use crate::{
    fft::EvaluationDomain,
    snark::marlin::{
        ahp::{
            indexer::CircuitInfo,
            verifier::{FirstMessage, QuerySet, SecondMessage, State, ThirdMessage},
            AHPError,
            AHPForR1CS,
        },
        params::OptimizationType,
        traits::FiatShamirRng,
        MarlinMode,
    },
};
use snarkvm_fields::PrimeField;

impl<TargetField: PrimeField, MM: MarlinMode> AHPForR1CS<TargetField, MM> {
    /// Output the first message and next round state.
    pub fn verifier_first_round<BaseField: PrimeField, R: FiatShamirRng<TargetField, BaseField>>(
        index_info: CircuitInfo<TargetField>,
        batch_size: usize,
        fs_rng: &mut R,
    ) -> Result<(FirstMessage<TargetField>, State<TargetField, MM>), AHPError> {
        // Check that the R1CS is a square matrix.
        if index_info.num_constraints != index_info.num_variables {
            return Err(AHPError::NonSquareMatrix);
        }

        let constraint_domain =
            EvaluationDomain::new(index_info.num_constraints).ok_or(AHPError::PolynomialDegreeTooLarge)?;

        let non_zero_a_domain =
            EvaluationDomain::new(index_info.num_non_zero_a).ok_or(AHPError::PolynomialDegreeTooLarge)?;

        let non_zero_b_domain =
            EvaluationDomain::new(index_info.num_non_zero_b).ok_or(AHPError::PolynomialDegreeTooLarge)?;
        let non_zero_c_domain =
            EvaluationDomain::new(index_info.num_non_zero_c).ok_or(AHPError::PolynomialDegreeTooLarge)?;

        let elems = fs_rng.squeeze_nonnative_field_elements(3 + batch_size - 1, OptimizationType::Weight)?;
        let (first, rest) = elems.split_at(3);
        let [alpha, eta_b, eta_c]: [_; 3] = first.try_into().unwrap();
        let mut batch_combiners = vec![TargetField::one()];
        batch_combiners.extend_from_slice(rest);
        assert!(!constraint_domain.evaluate_vanishing_polynomial(alpha).is_zero());

        let message = FirstMessage { alpha, eta_b, eta_c, batch_combiners };

        let new_state = State {
            batch_size,
            constraint_domain,
            non_zero_a_domain,
            non_zero_b_domain,
            non_zero_c_domain,
            first_round_message: Some(message.clone()),
            second_round_message: None,
            third_round_message: None,
            gamma: None,
            mode: PhantomData,
        };

        Ok((message, new_state))
    }

    /// Output the second message and next round state.
    pub fn verifier_second_round<BaseField: PrimeField, R: FiatShamirRng<TargetField, BaseField>>(
        mut state: State<TargetField, MM>,
        fs_rng: &mut R,
    ) -> Result<(SecondMessage<TargetField>, State<TargetField, MM>), AHPError> {
        let elems = fs_rng.squeeze_nonnative_field_elements(1, OptimizationType::Weight)?;
        let beta = elems[0];
        assert!(!state.constraint_domain.evaluate_vanishing_polynomial(beta).is_zero());

        let message = SecondMessage { beta };
        state.second_round_message = Some(message);

        Ok((message, state))
    }

    /// Output the third message and next round state.
    pub fn verifier_third_round<BaseField: PrimeField, R: FiatShamirRng<TargetField, BaseField>>(
        mut state: State<TargetField, MM>,
        fs_rng: &mut R,
    ) -> Result<(ThirdMessage<TargetField>, State<TargetField, MM>), AHPError> {
        let elems = fs_rng.squeeze_nonnative_field_elements(2, OptimizationType::Weight)?;
        let r_b = elems[0];
        let r_c = elems[1];
        let message = ThirdMessage { r_b, r_c };

        state.third_round_message = Some(message);
        Ok((message, state))
    }

    /// Output the third message and next round state.
    pub fn verifier_fourth_round<BaseField: PrimeField, R: FiatShamirRng<TargetField, BaseField>>(
        mut state: State<TargetField, MM>,
        fs_rng: &mut R,
    ) -> Result<State<TargetField, MM>, AHPError> {
        let elems = fs_rng.squeeze_nonnative_field_elements(1, OptimizationType::Weight)?;
        let gamma = elems[0];

        state.gamma = Some(gamma);
        Ok(state)
    }

    /// Output the query state and next round state.
    pub fn verifier_query_set(state: State<TargetField, MM>) -> (QuerySet<TargetField>, State<TargetField, MM>) {
        (QuerySet::new(&state), state)
    }
}
