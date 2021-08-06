// Copyright (C) 2019-2021 Aleo Systems Inc.
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
    ahp::{
        indexer::CircuitInfo,
        verifier::{VerifierFirstMessage, VerifierSecondMessage, VerifierState},
        AHPError,
        AHPForR1CS,
    },
    traits::FiatShamirRng,
};
use snarkvm_algorithms::fft::EvaluationDomain;
use snarkvm_fields::PrimeField;
use snarkvm_gadgets::nonnative::params::OptimizationType;
use snarkvm_r1cs::errors::SynthesisError;

use snarkvm_polycommit::QuerySet;

use rand_core::RngCore;

impl<TargetField: PrimeField> AHPForR1CS<TargetField> {
    /// Output the first message and next round state.
    pub fn verifier_first_round<BaseField: PrimeField, R: FiatShamirRng<TargetField, BaseField>>(
        index_info: CircuitInfo<TargetField>,
        fs_rng: &mut R,
    ) -> Result<(VerifierFirstMessage<TargetField>, VerifierState<TargetField>), AHPError> {
        // Check that the R1CS is a square matrix.
        if index_info.num_constraints != index_info.num_variables {
            return Err(AHPError::NonSquareMatrix);
        }

        let domain_h =
            EvaluationDomain::new(index_info.num_constraints).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let domain_k =
            EvaluationDomain::new(index_info.num_non_zero).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let elems = fs_rng.squeeze_nonnative_field_elements(4, OptimizationType::Weight)?;
        let alpha = elems[0];
        let eta_a = elems[1];
        let eta_b = elems[2];
        let eta_c = elems[3];
        assert!(!domain_h.evaluate_vanishing_polynomial(alpha).is_zero());

        let message = VerifierFirstMessage {
            alpha,
            eta_a,
            eta_b,
            eta_c,
        };

        let new_state = VerifierState {
            domain_h,
            domain_k,
            first_round_message: Some(message),
            second_round_message: None,
            gamma: None,
        };

        Ok((message, new_state))
    }

    /// Output the second message and next round state.
    pub fn verifier_second_round<BaseField: PrimeField, R: FiatShamirRng<TargetField, BaseField>>(
        mut state: VerifierState<TargetField>,
        fs_rng: &mut R,
    ) -> Result<(VerifierSecondMessage<TargetField>, VerifierState<TargetField>), AHPError> {
        let elems = fs_rng.squeeze_nonnative_field_elements(1, OptimizationType::Weight)?;
        let beta = elems[0];
        assert!(!state.domain_h.evaluate_vanishing_polynomial(beta).is_zero());

        let message = VerifierSecondMessage { beta };
        state.second_round_message = Some(message);

        Ok((message, state))
    }

    /// Output the third message and next round state.
    pub fn verifier_third_round<BaseField: PrimeField, R: FiatShamirRng<TargetField, BaseField>>(
        mut state: VerifierState<TargetField>,
        fs_rng: &mut R,
    ) -> Result<VerifierState<TargetField>, AHPError> {
        let elems = fs_rng.squeeze_nonnative_field_elements(1, OptimizationType::Weight)?;
        let gamma = elems[0];

        state.gamma = Some(gamma);
        Ok(state)
    }

    /// Output the query state and next round state.
    pub fn verifier_query_set<'a, 'b, R: RngCore>(
        state: VerifierState<TargetField>,
        _: &'a mut R,
        with_vanishing: bool,
    ) -> (QuerySet<'b, TargetField>, VerifierState<TargetField>) {
        let alpha = state.first_round_message.unwrap().alpha;
        let beta = state.second_round_message.unwrap().beta;
        let gamma = state.gamma.unwrap();

        let mut query_set = QuerySet::new();
        // For the first linear combination
        // Outer sumcheck test:
        //   s(beta) + r(alpha, beta) * (sum_M eta_M z_M(beta)) - t(beta) * z(beta)
        // = h_1(beta) * v_H(beta) + beta * g_1(beta)
        //
        // Note that z is the interpolation of x || w, so it equals x + v_X * w
        // We also use an optimization: instead of explicitly calculating z_c, we
        // use the "virtual oracle" z_b * z_c
        //
        // LinearCombination::new(
        //      outer_sumcheck
        //      vec![
        //          (F::one(), "mask_poly".into()),
        //
        //          (r_alpha_at_beta * (eta_a + eta_c * z_b_at_beta), "z_a".into()),
        //          (r_alpha_at_beta * eta_b * z_b_at_beta, LCTerm::One),
        //
        //          (-t_at_beta * v_X_at_beta, "w".into()),
        //          (-t_at_beta * x_at_beta, LCTerm::One),
        //
        //          (-v_H_at_beta, "h_1".into()),
        //          (-beta * g_1_at_beta, LCTerm::One),
        //      ],
        //  )
        //  LinearCombination::new("z_b", vec![(F::one(), z_b)])
        //  LinearCombination::new("g_1", vec![(F::one(), g_1)], rhs::new(g_1_at_beta))
        //  LinearCombination::new("t", vec![(F::one(), t)])
        query_set.insert(("g_1".into(), ("beta".into(), beta)));
        query_set.insert(("z_b".into(), ("beta".into(), beta)));
        query_set.insert(("t".into(), ("beta".into(), beta)));
        query_set.insert(("outer_sumcheck".into(), ("beta".into(), beta)));

        // For the second linear combination
        // Inner sumcheck test:
        //   h_2(gamma) * v_K(gamma)
        // = a(gamma) - b(gamma) * (gamma g_2(gamma) + t(beta) / |K|)
        //
        // where
        //   a(X) := sum_M (eta_M v_H(beta) v_H(alpha) val_M(X))
        //   b(X) := (beta - row(X)) (alpha - col(X))
        //
        // LinearCombination::new("g_2", vec![(F::one(), g_2)]);
        //
        // LinearCombination::new(
        //     "denom".into(),
        //     vec![
        //         (alpha * beta, LCTerm::One),
        //         (-alpha, "row"),
        //         (-beta, "col"),
        //         (F::one(), "row_col"),
        // ]);
        //
        // LinearCombination::new(
        //     "a_poly".into(),
        //     vec![
        //          (eta_a * "a_val".into()),
        //          (eta_b * "b_val".into()),
        //          (eta_c * "c_val".into()),
        //      ],
        //  )
        //
        // let v_H_at_alpha = domain_h.evaluate_vanishing_polynomial(alpha);
        // let v_H_at_beta = domain_h.evaluate_vanishing_polynomial(beta);
        // let v_K_at_gamma = domain_k.evaluate_vanishing_polynomial(gamma);
        //
        // let a_poly_lc *= v_H_at_alpha * v_H_at_beta;
        // let b_lc = denom
        // let h_lc = LinearCombination::new("b_poly", vec![(v_K_at_gamma, "h_2")]);
        //
        // // This LC is the only one that is evaluated:
        // let inner_sumcheck = a_poly_lc - (b_lc * (gamma * g_2_at_gamma + (t_at_beta / &k_size))) - h_lc
        // main_lc.set_label("inner_sumcheck");
        query_set.insert(("g_2".into(), ("gamma".into(), gamma)));
        query_set.insert(("inner_sumcheck".into(), ("gamma".into(), gamma)));

        if with_vanishing {
            query_set.insert(("vanishing_poly_h_alpha".into(), ("alpha".into(), alpha)));
            query_set.insert(("vanishing_poly_h_beta".into(), ("beta".into(), beta)));
            query_set.insert(("vanishing_poly_k_gamma".into(), ("gamma".into(), gamma)));
        }

        (query_set, state)
    }
}
