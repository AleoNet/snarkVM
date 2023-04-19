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

use core::marker::PhantomData;

use crate::{
    fft::EvaluationDomain,
    snark::marlin::{
        ahp::{
            indexer::{CircuitId, CircuitInfo},
            verifier::{BatchCombiners, FirstMessage, QuerySet, SecondMessage, State, ThirdMessage},
            AHPError,
            AHPForR1CS,
        },
        verifier::CircuitSpecificState,
        MarlinMode,
    },
    AlgebraicSponge,
};
use smallvec::SmallVec;
use snarkvm_fields::PrimeField;
use std::collections::BTreeMap;

impl<TargetField: PrimeField, MM: MarlinMode> AHPForR1CS<TargetField, MM> {
    /// Output the first message and next round state.
    pub fn verifier_first_round<BaseField: PrimeField, R: AlgebraicSponge<BaseField, 2>>(
        batch_sizes: &BTreeMap<CircuitId, usize>,
        circuit_infos: &BTreeMap<CircuitId, &CircuitInfo<TargetField>>,
        max_constraint_domain: EvaluationDomain<TargetField>,
        largest_non_zero_domain: EvaluationDomain<TargetField>,
        fs_rng: &mut R,
    ) -> Result<(FirstMessage<TargetField>, State<TargetField, MM>), AHPError> {
        let elems = fs_rng.squeeze_nonnative_field_elements(3);
        let (first, _) = elems.split_at(3);
        let [alpha, eta_b, eta_c]: [_; 3] = first.try_into().unwrap();
        let mut batch_combiners = BTreeMap::new();
        let mut circuit_specific_states = BTreeMap::new();
        let mut num_circuit_combiners = vec![1; batch_sizes.len()];
        num_circuit_combiners[0] = 0; // the first circuit_combiner is TargetField::one() and needs no random sampling

        for ((batch_size, (circuit_id, circuit_info)), num_c_combiner) in
            batch_sizes.values().zip(circuit_infos).zip(num_circuit_combiners)
        {
            let squeeze_time = start_timer!(|| format!("Squeezing challenges for {circuit_id}"));
            let elems = fs_rng.squeeze_nonnative_field_elements(*batch_size - 1 + num_c_combiner);
            end_timer!(squeeze_time);

            let (instance_combiners, circuit_combiner) = elems.split_at(*batch_size - 1);
            assert_eq!(circuit_combiner.len(), num_c_combiner);
            let mut combiners =
                BatchCombiners { circuit_combiner: TargetField::one(), instance_combiners: vec![TargetField::one()] };
            if num_c_combiner == 1 {
                combiners.circuit_combiner = circuit_combiner[0];
            }
            combiners.instance_combiners.extend(instance_combiners);
            batch_combiners.insert(*circuit_id, combiners);

            // Check that the R1CS is a square matrix.
            if circuit_info.num_constraints != circuit_info.num_variables {
                return Err(AHPError::NonSquareMatrix);
            }

            let constraint_domain_time = start_timer!(|| format!("Constructing constraint domain for {circuit_id}"));
            let constraint_domain =
                EvaluationDomain::new(circuit_info.num_constraints).ok_or(AHPError::PolynomialDegreeTooLarge)?;
            end_timer!(constraint_domain_time);

            let non_zero_a_time = start_timer!(|| format!("Constructing non-zero-a domain for {circuit_id}"));
            let non_zero_a_domain =
                EvaluationDomain::new(circuit_info.num_non_zero_a).ok_or(AHPError::PolynomialDegreeTooLarge)?;
            end_timer!(non_zero_a_time);

            let non_zero_b_time = start_timer!(|| format!("Constructing non-zero-b domain {circuit_id}"));
            let non_zero_b_domain =
                EvaluationDomain::new(circuit_info.num_non_zero_b).ok_or(AHPError::PolynomialDegreeTooLarge)?;
            end_timer!(non_zero_b_time);

            let non_zero_c_time = start_timer!(|| format!("Constructing non-zero-c domain for {circuit_id}"));
            let non_zero_c_domain =
                EvaluationDomain::new(circuit_info.num_non_zero_c).ok_or(AHPError::PolynomialDegreeTooLarge)?;
            end_timer!(non_zero_c_time);

            let input_domain_time = start_timer!(|| format!("Constructing input domain {circuit_id}"));
            let input_domain =
                EvaluationDomain::new(circuit_info.num_public_inputs).ok_or(AHPError::PolynomialDegreeTooLarge)?;
            end_timer!(input_domain_time);

            let circuit_specific_state = CircuitSpecificState {
                input_domain,
                constraint_domain,
                non_zero_a_domain,
                non_zero_b_domain,
                non_zero_c_domain,
                batch_size: *batch_size,
            };
            circuit_specific_states.insert(*circuit_id, circuit_specific_state);
        }

        let check_vanish_poly_time = start_timer!(|| "Evaluating vanishing polynomial");
        assert!(!max_constraint_domain.evaluate_vanishing_polynomial(alpha).is_zero());
        end_timer!(check_vanish_poly_time);

        let message = FirstMessage { alpha, eta_b, eta_c, batch_combiners };

        let new_state = State {
            circuit_specific_states,
            max_constraint_domain,
            largest_non_zero_domain,

            first_round_message: Some(message.clone()),
            second_round_message: None,
            third_round_message: None,

            gamma: None,
            mode: PhantomData,
        };

        Ok((message, new_state))
    }

    /// Output the second message and next round state.
    pub fn verifier_second_round<BaseField: PrimeField, R: AlgebraicSponge<BaseField, 2>>(
        mut state: State<TargetField, MM>,
        fs_rng: &mut R,
    ) -> Result<(SecondMessage<TargetField>, State<TargetField, MM>), AHPError> {
        let elems = fs_rng.squeeze_nonnative_field_elements(1);
        let beta = elems[0];
        assert!(!state.max_constraint_domain.evaluate_vanishing_polynomial(beta).is_zero());

        let message = SecondMessage { beta };
        state.second_round_message = Some(message);

        Ok((message, state))
    }

    /// Output the third message and next round state.
    pub fn verifier_third_round<BaseField: PrimeField, R: AlgebraicSponge<BaseField, 2>>(
        mut state: State<TargetField, MM>,
        fs_rng: &mut R,
    ) -> Result<(ThirdMessage<TargetField>, State<TargetField, MM>), AHPError> {
        let num_circuits = state.circuit_specific_states.len();
        let mut delta_a = Vec::with_capacity(num_circuits);
        let mut delta_b = Vec::with_capacity(num_circuits);
        let mut delta_c = Vec::with_capacity(num_circuits);
        let first_elems = fs_rng.squeeze_nonnative_field_elements(2);
        delta_a.push(TargetField::one());
        delta_b.push(first_elems[0]);
        delta_c.push(first_elems[1]);
        for _ in 1..num_circuits {
            let elems: SmallVec<[TargetField; 10]> = fs_rng.squeeze_nonnative_field_elements(3);
            delta_a.push(elems[0]);
            delta_b.push(elems[1]);
            delta_c.push(elems[2]);
        }
        let message = ThirdMessage { delta_a, delta_b, delta_c };

        state.third_round_message = Some(message.clone());
        Ok((message, state))
    }

    /// Output the next round state.
    pub fn verifier_fourth_round<BaseField: PrimeField, R: AlgebraicSponge<BaseField, 2>>(
        mut state: State<TargetField, MM>,
        fs_rng: &mut R,
    ) -> Result<State<TargetField, MM>, AHPError> {
        let elems = fs_rng.squeeze_nonnative_field_elements(1);
        let gamma = elems[0];

        state.gamma = Some(gamma);
        Ok(state)
    }

    /// Output the query state and next round state.
    pub fn verifier_query_set(state: State<TargetField, MM>) -> (QuerySet<TargetField>, State<TargetField, MM>) {
        (QuerySet::new(&state), state)
    }
}
