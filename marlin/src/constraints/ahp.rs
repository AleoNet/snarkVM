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
    ahp::errors::AHPError,
    constraints::{
        data_structures::{PreparedCircuitVerifyingKeyVar, ProofVar},
        lagrange_interpolation::LagrangeInterpolationVar,
        polynomial::AlgebraForAHP,
    },
    fiat_shamir::{constraints::FiatShamirRngVar, FiatShamirRng},
    PhantomData, String, ToString, Vec,
};
use snarkvm_fields::PrimeField;
use snarkvm_gadgets::{
    fields::FpGadget,
    traits::{
        fields::{FieldGadget, ToConstraintFieldGadget},
        utilities::boolean::Boolean,
    },
    utilities::{alloc::AllocGadget, eq::NEqGadget},
};
use snarkvm_nonnative::{params::OptimizationType, NonNativeFieldVar};
use snarkvm_polycommit::{
    constraints::{
        EvaluationsVar, LabeledPointVar, LinearCombinationCoeffVar, LinearCombinationVar, PCCheckVar, PrepareGadget,
        QuerySetVar,
    },
    LCTerm, PolynomialCommitment,
};
use snarkvm_r1cs::ConstraintSystem;

use hashbrown::{HashMap, HashSet};

#[derive(Clone)]
pub struct VerifierStateVar<TargetField: PrimeField, BaseField: PrimeField> {
    domain_h_size: u64,
    domain_k_size: u64,

    first_round_msg: Option<VerifierFirstMsgVar<TargetField, BaseField>>,
    second_round_msg: Option<VerifierSecondMsgVar<TargetField, BaseField>>,

    gamma: Option<NonNativeFieldVar<TargetField, BaseField>>,
}

#[derive(Clone)]
pub struct VerifierFirstMsgVar<TargetField: PrimeField, BaseField: PrimeField> {
    pub alpha: NonNativeFieldVar<TargetField, BaseField>,
    pub eta_a: NonNativeFieldVar<TargetField, BaseField>,
    pub eta_b: NonNativeFieldVar<TargetField, BaseField>,
    pub eta_c: NonNativeFieldVar<TargetField, BaseField>,
}

#[derive(Clone)]
pub struct VerifierSecondMsgVar<TargetField: PrimeField, BaseField: PrimeField> {
    pub beta: NonNativeFieldVar<TargetField, BaseField>,
}

#[derive(Clone)]
pub struct VerifierThirdMsgVar<TargetField: PrimeField, BaseField: PrimeField> {
    pub gamma: NonNativeFieldVar<TargetField, BaseField>,
}

pub struct AHPForR1CS<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
> where
    PCG::VerifierKeyVar: ToConstraintFieldGadget<BaseField>,
    PCG::CommitmentVar: ToConstraintFieldGadget<BaseField>,
{
    field: PhantomData<TargetField>,
    constraint_field: PhantomData<BaseField>,
    polynomial_commitment: PhantomData<PC>,
    pc_check: PhantomData<PCG>,
}

impl<
        TargetField: PrimeField,
        BaseField: PrimeField,
        PC: PolynomialCommitment<TargetField>,
        PCG: PCCheckVar<TargetField, PC, BaseField>,
    > AHPForR1CS<TargetField, BaseField, PC, PCG>
where
    PCG::VerifierKeyVar: ToConstraintFieldGadget<BaseField>,
    PCG::CommitmentVar: ToConstraintFieldGadget<BaseField>,
{
    /// Output the first message and next round state.
    #[allow(clippy::type_complexity)]
    pub fn verifier_first_round<
        CS: ConstraintSystem<BaseField>,
        CommitmentVar: ToConstraintFieldGadget<BaseField>,
        PR: FiatShamirRng<TargetField, BaseField>,
        R: FiatShamirRngVar<TargetField, BaseField, PR>,
    >(
        cs: CS,
        domain_h_size: u64,
        domain_k_size: u64,
        fs_rng: &mut R,
        comms: &[CommitmentVar],
        message: &[NonNativeFieldVar<TargetField, BaseField>],
    ) -> anyhow::Result<(
        VerifierFirstMsgVar<TargetField, BaseField>,
        VerifierStateVar<TargetField, BaseField>,
    )> {
        // absorb the first commitments and messages
        {
            let mut elems = Vec::<FpGadget<BaseField>>::new();
            comms.iter().for_each(|comm| {
                elems.append(&mut comm.to_constraint_field().unwrap());
            });
            fs_rng.absorb_native_field_elements(cs.ns(|| "absorb_native_field_elements"), &elems)?;
            fs_rng.absorb_nonnative_field_elements(
                cs.ns(|| "absorb_nonnative_field_elements"),
                &message,
                OptimizationType::Weight,
            )?;
        }

        // obtain four elements from the sponge
        let elems = fs_rng.squeeze_field_elements(cs.ns(|| "squeeze_field_elements"), 4)?;
        let alpha = elems[0].clone();
        let eta_a = elems[1].clone();
        let eta_b = elems[2].clone();
        let eta_c = elems[3].clone();

        let msg = VerifierFirstMsgVar {
            alpha,
            eta_a,
            eta_b,
            eta_c,
        };

        let new_state = VerifierStateVar {
            domain_h_size,
            domain_k_size,
            first_round_msg: Some(msg.clone()),
            second_round_msg: None,
            gamma: None,
        };

        Ok((msg, new_state))
    }

    #[allow(clippy::type_complexity)]
    pub fn verifier_second_round<
        CS: ConstraintSystem<BaseField>,
        CommitmentVar: ToConstraintFieldGadget<BaseField>,
        PR: FiatShamirRng<TargetField, BaseField>,
        R: FiatShamirRngVar<TargetField, BaseField, PR>,
    >(
        cs: CS,
        state: VerifierStateVar<TargetField, BaseField>,
        fs_rng: &mut R,
        comms: &[CommitmentVar],
        message: &[NonNativeFieldVar<TargetField, BaseField>],
    ) -> anyhow::Result<(
        VerifierSecondMsgVar<TargetField, BaseField>,
        VerifierStateVar<TargetField, BaseField>,
    )> {
        let VerifierStateVar {
            domain_h_size,
            domain_k_size,
            first_round_msg,
            ..
        } = state;

        // absorb the second commitments and messages
        {
            let mut elems = Vec::<FpGadget<BaseField>>::new();
            comms.iter().for_each(|comm| {
                elems.append(&mut comm.to_constraint_field().unwrap());
            });
            fs_rng.absorb_native_field_elements(cs.ns(|| "absorb_native_field_elements"), &elems)?;
            fs_rng.absorb_nonnative_field_elements(
                cs.ns(|| "absorb_nonnative_field_elements"),
                &message,
                OptimizationType::Weight,
            )?;
        }

        // obtain one element from the sponge
        let elems = fs_rng.squeeze_field_elements(cs.ns(|| "squeeze_field_elements"), 1)?;
        let beta = elems[0].clone();

        let msg = VerifierSecondMsgVar { beta };

        let new_state = VerifierStateVar {
            domain_h_size,
            domain_k_size,
            first_round_msg,
            second_round_msg: Some(msg.clone()),
            gamma: None,
        };

        Ok((msg, new_state))
    }

    pub fn verifier_third_round<
        CS: ConstraintSystem<BaseField>,
        CommitmentVar: ToConstraintFieldGadget<BaseField>,
        PR: FiatShamirRng<TargetField, BaseField>,
        R: FiatShamirRngVar<TargetField, BaseField, PR>,
    >(
        cs: CS,
        state: VerifierStateVar<TargetField, BaseField>,
        fs_rng: &mut R,
        comms: &[CommitmentVar],
        message: &[NonNativeFieldVar<TargetField, BaseField>],
    ) -> anyhow::Result<VerifierStateVar<TargetField, BaseField>> {
        let VerifierStateVar {
            domain_h_size,
            domain_k_size,
            first_round_msg,
            second_round_msg,
            ..
        } = state;

        // absorb the third commitments and messages
        {
            let mut elems = Vec::<FpGadget<BaseField>>::new();
            comms.iter().for_each(|comm| {
                elems.append(&mut comm.to_constraint_field().unwrap());
            });
            fs_rng.absorb_native_field_elements(cs.ns(|| "absorb_native_field_elements"), &elems)?;
            fs_rng.absorb_nonnative_field_elements(
                cs.ns(|| "absorb_nonnative_field_elements"),
                &message,
                OptimizationType::Weight,
            )?;
        }

        // obtain one element from the sponge
        let elems = fs_rng.squeeze_field_elements(cs.ns(|| "squeeze_field_elements"), 1)?;
        let gamma = elems[0].clone();

        let new_state = VerifierStateVar {
            domain_h_size,
            domain_k_size,
            first_round_msg,
            second_round_msg,
            gamma: Some(gamma),
        };

        Ok(new_state)
    }

    pub fn verifier_decision<CS: ConstraintSystem<BaseField>>(
        mut cs: CS,
        public_input: &[NonNativeFieldVar<TargetField, BaseField>],
        evals: &HashMap<String, NonNativeFieldVar<TargetField, BaseField>>,
        state: VerifierStateVar<TargetField, BaseField>,
        domain_k_size_in_vk: &FpGadget<BaseField>,
    ) -> anyhow::Result<Vec<LinearCombinationVar<TargetField, BaseField>>> {
        let VerifierStateVar {
            domain_k_size,
            first_round_msg,
            second_round_msg,
            gamma,
            ..
        } = state;

        let first_round_msg =
            first_round_msg.expect("VerifierState should include first_round_msg when verifier_decision is called");
        let second_round_msg =
            second_round_msg.expect("VerifierState should include second_round_msg when verifier_decision is called");

        let zero = NonNativeFieldVar::<TargetField, BaseField>::zero(cs.ns(|| "nonnative_zero"))?;

        let VerifierFirstMsgVar {
            alpha,
            eta_a,
            eta_b,
            eta_c,
        } = first_round_msg;
        let beta: NonNativeFieldVar<TargetField, BaseField> = second_round_msg.beta;

        let v_h_at_alpha = evals
            .get("vanishing_poly_h_alpha")
            .ok_or_else(|| AHPError::MissingEval("vanishing_poly_h_alpha".to_string()).into())?;

        v_h_at_alpha.enforce_not_equal(cs.ns(|| "v_h_at_alpha_enforce_not_zero"), &zero)?;

        let v_h_at_beta = evals
            .get("vanishing_poly_h_beta")
            .ok_or_else(|| AHPError::MissingEval("vanishing_poly_h_beta".to_string()).into())?;
        v_h_at_beta.enforce_not_equal(cs.ns(|| "v_h_at_beta_enforce_not_zero"), &zero)?;

        let gamma: NonNativeFieldVar<TargetField, BaseField> =
            gamma.expect("VerifierState should include gamma when verifier_decision is called");

        let t_at_beta = evals
            .get("t")
            .ok_or_else(|| AHPError::MissingEval("t".to_string()).into())?;

        let v_k_at_gamma = evals
            .get("vanishing_poly_k_gamma")
            .ok_or_else(|| AHPError::MissingEval("vanishing_poly_k_gamma".to_string()).into())?;

        let r_alpha_at_beta = AlgebraForAHP::prepared_eval_bivariable_vanishing_polynomial(
            cs.ns(|| "prepared_eval_bivariable_vanishing_polynomial"),
            &alpha,
            &beta,
            &v_h_at_alpha,
            &v_h_at_beta,
        )?;

        let z_b_at_beta = evals
            .get("z_b")
            .ok_or_else(|| AHPError::MissingEval("z_b".to_string()).into())?;

        let x_padded_len = public_input.len().next_power_of_two() as u64;

        let mut interpolation_gadget = LagrangeInterpolationVar::<TargetField, BaseField>::new(
            TargetField::get_root_of_unity(x_padded_len as usize).unwrap(),
            x_padded_len,
            public_input,
        );

        let f_x_at_beta = interpolation_gadget.interpolate_constraints(cs.ns(|| "interpolate_constraints"), &beta)?;

        let g_1_at_beta = evals
            .get("g_1")
            .ok_or_else(|| AHPError::MissingEval("g_1".to_string()).into())?;

        // Compute linear combinations
        let mut linear_combinations = Vec::new();

        // Only compute for linear combination optimization.
        let pow_x_at_beta = AlgebraForAHP::prepare(cs.ns(|| "prepare"), &beta, x_padded_len)?;
        let v_x_at_beta = AlgebraForAHP::prepared_eval_vanishing_polynomial(
            cs.ns(|| "prepared_eval_vanishing_polynomial"),
            &pow_x_at_beta,
        )?;

        // Outer sumcheck
        let z_b_lc_gadget = LinearCombinationVar::<TargetField, BaseField> {
            label: "z_b".to_string(),
            terms: vec![(LinearCombinationCoeffVar::One, "z_b".into())],
        };

        let g_1_lc_gadget = LinearCombinationVar::<TargetField, BaseField> {
            label: "g_1".to_string(),
            terms: vec![(LinearCombinationCoeffVar::One, "g_1".into())],
        };

        let t_lc_gadget = LinearCombinationVar::<TargetField, BaseField> {
            label: "t".to_string(),
            terms: vec![(LinearCombinationCoeffVar::One, "t".into())],
        };

        let eta_c_mul_z_b_at_beta = eta_c.mul(cs.ns(|| "eta_c_mul_z_b_at_beta"), &z_b_at_beta)?;
        let eta_a_add_above = eta_a.add(cs.ns(|| "eta_a_add_eta_c"), &eta_c_mul_z_b_at_beta)?;

        let outer_sumcheck_lc_gadget = LinearCombinationVar::<TargetField, BaseField> {
            label: "outer_sumcheck".to_string(),
            terms: vec![
                (LinearCombinationCoeffVar::One, "mask_poly".into()),
                (
                    LinearCombinationCoeffVar::Var(
                        r_alpha_at_beta.mul(cs.ns(|| "r_alpha_mul_eta_a"), &eta_a_add_above)?,
                    ),
                    "z_a".into(),
                ),
                (
                    LinearCombinationCoeffVar::Var(
                        r_alpha_at_beta
                            .mul(cs.ns(|| "r_alpha_at_beta_mul_eta_b"), &eta_b)?
                            .mul(cs.ns(|| "r_alpha_at_beta_mul_eta_b_mul_z_b_at_beta"), &z_b_at_beta)?,
                    ),
                    LCTerm::One,
                ),
                (
                    LinearCombinationCoeffVar::Var(
                        t_at_beta
                            .mul(cs.ns(|| "t_at_beta_mul_v_x_at_beta"), &v_x_at_beta)?
                            .negate(cs.ns(|| "negate_t_v"))?,
                    ),
                    "w".into(),
                ),
                (
                    LinearCombinationCoeffVar::Var(
                        t_at_beta
                            .mul(cs.ns(|| "t_at_beta_mul_f_x_at_beta"), &f_x_at_beta)?
                            .negate(cs.ns(|| "negate_t_f"))?,
                    ),
                    LCTerm::One,
                ),
                (
                    LinearCombinationCoeffVar::Var(v_h_at_beta.negate(cs.ns(|| "negate_v_h"))?),
                    "h_1".into(),
                ),
                (
                    LinearCombinationCoeffVar::Var(
                        (beta.mul(cs.ns(|| "beta_mul_g_1_at_beta"), &g_1_at_beta))?
                            .negate(cs.ns(|| "negate_beta_g1"))?,
                    ),
                    LCTerm::One,
                ),
            ],
        };

        linear_combinations.push(g_1_lc_gadget);
        linear_combinations.push(z_b_lc_gadget);
        linear_combinations.push(t_lc_gadget);
        linear_combinations.push(outer_sumcheck_lc_gadget);

        // Inner sumcheck
        let g_2_lc_gadget = LinearCombinationVar::<TargetField, BaseField> {
            label: "g_2".to_string(),
            terms: vec![(LinearCombinationCoeffVar::One, "g_2".into())],
        };

        let beta_alpha = beta.mul(cs.ns(|| "beta_mul_alpha"), &alpha)?;

        let a_denom_lc_gadget = LinearCombinationVar::<TargetField, BaseField> {
            label: "a_denom".to_string(),
            terms: vec![
                (LinearCombinationCoeffVar::Var(beta_alpha.clone()), LCTerm::One),
                (
                    LinearCombinationCoeffVar::Var(alpha.negate(cs.ns(|| "a_alpha"))?),
                    "a_row".into(),
                ),
                (
                    LinearCombinationCoeffVar::Var(beta.negate(cs.ns(|| "a_beta"))?),
                    "a_col".into(),
                ),
                (LinearCombinationCoeffVar::One, "a_row_col".into()),
            ],
        };

        let b_denom_lc_gadget = LinearCombinationVar::<TargetField, BaseField> {
            label: "b_denom".to_string(),
            terms: vec![
                (LinearCombinationCoeffVar::Var(beta_alpha.clone()), LCTerm::One),
                (
                    LinearCombinationCoeffVar::Var(alpha.negate(cs.ns(|| "b_alpha"))?),
                    "b_row".into(),
                ),
                (
                    LinearCombinationCoeffVar::Var(beta.negate(cs.ns(|| "b_beta"))?),
                    "b_col".into(),
                ),
                (LinearCombinationCoeffVar::One, "b_row_col".into()),
            ],
        };

        let c_denom_lc_gadget = LinearCombinationVar::<TargetField, BaseField> {
            label: "c_denom".to_string(),
            terms: vec![
                (LinearCombinationCoeffVar::Var(beta_alpha.clone()), LCTerm::One),
                (
                    LinearCombinationCoeffVar::Var(alpha.negate(cs.ns(|| "c_alpha"))?),
                    "c_row".into(),
                ),
                (
                    LinearCombinationCoeffVar::Var(beta.negate(cs.ns(|| "c_beta"))?),
                    "c_col".into(),
                ),
                (LinearCombinationCoeffVar::One, "c_row_col".into()),
            ],
        };

        let a_denom_at_gamma = evals.get(&a_denom_lc_gadget.label).unwrap();
        let b_denom_at_gamma = evals.get(&b_denom_lc_gadget.label).unwrap();
        let c_denom_at_gamma = evals.get(&c_denom_lc_gadget.label).unwrap();
        let g_2_at_gamma = evals.get(&g_2_lc_gadget.label).unwrap();

        let v_h_at_alpha_beta = v_h_at_alpha.mul(cs.ns(|| "v_h_alpha_mul_v_h_beta"), &v_h_at_beta)?;

        let domain_k_size_gadget = NonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| "domain_k"), || {
            Ok(TargetField::from(domain_k_size as u128))
        })?;
        let inv_domain_k_size_gadget = domain_k_size_gadget.inverse(cs.ns(|| "domain_k_inverse"))?;

        let domain_k_size_bit_decomposition =
            domain_k_size_gadget.to_bits_le(cs.ns(|| "domain_k_gadget_to_bits_le"))?;

        let domain_k_size_in_vk_bit_decomposition =
            domain_k_size_in_vk.to_bits_le(cs.ns(|| "domain_k_size_in_vk_to_bits_le"))?;

        // This is not the most efficient implementation; an alternative is to check if the last limb of domain_k_size_gadget
        // can be bit composed by the bits in domain_k_size_in_vk, which would save a lot of constraints.
        // Nevertheless, doing so is using the nonnative field gadget in a non-black-box manner and is somehow not encouraged.
        for (i, (left, right)) in domain_k_size_bit_decomposition
            .iter()
            .take(32)
            .zip(domain_k_size_in_vk_bit_decomposition.iter())
            .enumerate()
        {
            left.enforce_equal(cs.ns(|| format!("domain_k_enforce_equal_{}", i)), &right)?;
        }

        for (i, bit) in domain_k_size_bit_decomposition.iter().skip(32).enumerate() {
            bit.enforce_equal(
                cs.ns(|| format!("domain_k_enforce_false_{}", i)),
                &Boolean::constant(false),
            )?;
        }

        let gamma_mul_g_2 = gamma.mul(cs.ns(|| "gamma_mul_g_2"), &g_2_at_gamma)?;
        let t_div_domain_k = t_at_beta.mul(cs.ns(|| "t_div_domain_k"), &inv_domain_k_size_gadget)?;
        let b_expr_at_gamma_last_term = gamma_mul_g_2.add(cs.ns(|| "b_expr_at_gamma_last_term"), &t_div_domain_k)?;
        let ab_denom_at_gamma = a_denom_at_gamma.mul(cs.ns(|| "ab_denom_at_gamma"), &b_denom_at_gamma)?;

        let inner_sumcheck_lc_gadget = LinearCombinationVar::<TargetField, BaseField> {
            label: "inner_sumcheck".to_string(),
            terms: vec![
                (
                    LinearCombinationCoeffVar::Var(
                        eta_a
                            .mul(cs.ns(|| "eta_a_mul_b_denom"), &b_denom_at_gamma)?
                            .mul(cs.ns(|| "eta_a_mul_b_denom_mul_c_denom"), &c_denom_at_gamma)?
                            .mul(cs.ns(|| "eta_a_mul_b_denom_mul_c_denom_mul_v_h"), &v_h_at_alpha_beta)?,
                    ),
                    "a_val".into(),
                ),
                (
                    LinearCombinationCoeffVar::Var(
                        eta_b
                            .mul(cs.ns(|| "eta_b_mul_a_denom"), &a_denom_at_gamma)?
                            .mul(cs.ns(|| "eta_b_mul_a_denom_mul_c_denom"), &c_denom_at_gamma)?
                            .mul(cs.ns(|| "eta_b_mul_a_denom_mul_c_denom_mul_v_h"), &v_h_at_alpha_beta)?,
                    ),
                    "b_val".into(),
                ),
                (
                    LinearCombinationCoeffVar::Var(
                        eta_c
                            .mul(cs.ns(|| "eta_c_mul_ab_denom"), &ab_denom_at_gamma)?
                            .mul(cs.ns(|| "eta_c_mul_ab_denom_mul_v_h"), &v_h_at_alpha_beta)?,
                    ),
                    "c_val".into(),
                ),
                (
                    LinearCombinationCoeffVar::Var(
                        ab_denom_at_gamma
                            .mul(cs.ns(|| "ab_denom_mul_c_denom"), &c_denom_at_gamma)?
                            .mul(cs.ns(|| "ab_denom_mul_c_denom_mul_b_last"), &b_expr_at_gamma_last_term)?
                            .negate(cs.ns(|| "ab_c_b_negate"))?,
                    ),
                    LCTerm::One,
                ),
                (
                    LinearCombinationCoeffVar::Var(v_k_at_gamma.negate(cs.ns(|| "v_k_negate"))?),
                    "h_2".into(),
                ),
            ],
        };

        linear_combinations.push(g_2_lc_gadget);
        linear_combinations.push(a_denom_lc_gadget);
        linear_combinations.push(b_denom_lc_gadget);
        linear_combinations.push(c_denom_lc_gadget);
        linear_combinations.push(inner_sumcheck_lc_gadget);

        let vanishing_poly_h_alpha_lc_gadget = LinearCombinationVar::<TargetField, BaseField> {
            label: "vanishing_poly_h_alpha".to_string(),
            terms: vec![(LinearCombinationCoeffVar::One, "vanishing_poly_h".into())],
        };
        let vanishing_poly_h_beta_lc_gadget = LinearCombinationVar::<TargetField, BaseField> {
            label: "vanishing_poly_h_beta".to_string(),
            terms: vec![(LinearCombinationCoeffVar::One, "vanishing_poly_h".into())],
        };
        let vanishing_poly_k_gamma_lc_gadget = LinearCombinationVar::<TargetField, BaseField> {
            label: "vanishing_poly_k_gamma".to_string(),
            terms: vec![(LinearCombinationCoeffVar::One, "vanishing_poly_k".into())],
        };
        linear_combinations.push(vanishing_poly_h_alpha_lc_gadget);
        linear_combinations.push(vanishing_poly_h_beta_lc_gadget);
        linear_combinations.push(vanishing_poly_k_gamma_lc_gadget);

        linear_combinations.sort_by(|a, b| a.label.cmp(&b.label));

        Ok(linear_combinations)
    }

    #[allow(clippy::type_complexity)]
    pub fn verifier_comm_query_eval_set<
        CS: ConstraintSystem<BaseField>,
        PR: FiatShamirRng<TargetField, BaseField>,
        R: FiatShamirRngVar<TargetField, BaseField, PR>,
    >(
        cs: CS,
        index_pvk: &PreparedCircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG, PR, R>,
        proof: &ProofVar<TargetField, BaseField, PC, PCG>,
        state: &VerifierStateVar<TargetField, BaseField>,
    ) -> anyhow::Result<(
        usize,
        usize,
        Vec<PCG::PreparedLabeledCommitmentVar>,
        QuerySetVar<TargetField, BaseField>,
        EvaluationsVar<TargetField, BaseField>,
    )> {
        let VerifierStateVar {
            first_round_msg,
            second_round_msg,
            gamma,
            ..
        } = state;

        let first_round_msg = first_round_msg
            .as_ref()
            .expect("VerifierState should include first_round_msg when verifier_query_set is called");

        let second_round_msg = second_round_msg
            .as_ref()
            .expect("VerifierState should include second_round_msg when verifier_query_set is called");

        let alpha = first_round_msg.alpha.clone();

        let beta = second_round_msg.beta.clone();

        let gamma_ref = gamma
            .as_ref()
            .expect("VerifierState should include gamma when verifier_query_set is called")
            .clone();

        let gamma = gamma_ref;

        let mut query_set_gadget = QuerySetVar::<TargetField, BaseField> { 0: HashSet::new() };

        query_set_gadget.0.insert((
            "g_1".to_string(),
            LabeledPointVar {
                name: "beta".to_string(),
                value: beta.clone(),
            },
        ));
        query_set_gadget.0.insert((
            "z_b".to_string(),
            LabeledPointVar {
                name: "beta".to_string(),
                value: beta.clone(),
            },
        ));
        query_set_gadget.0.insert((
            "t".to_string(),
            LabeledPointVar {
                name: "beta".to_string(),
                value: beta.clone(),
            },
        ));
        query_set_gadget.0.insert((
            "outer_sumcheck".to_string(),
            LabeledPointVar {
                name: "beta".to_string(),
                value: beta.clone(),
            },
        ));
        query_set_gadget.0.insert((
            "g_2".to_string(),
            LabeledPointVar {
                name: "gamma".to_string(),
                value: gamma.clone(),
            },
        ));
        query_set_gadget.0.insert((
            "a_denom".to_string(),
            LabeledPointVar {
                name: "gamma".to_string(),
                value: gamma.clone(),
            },
        ));
        query_set_gadget.0.insert((
            "b_denom".to_string(),
            LabeledPointVar {
                name: "gamma".to_string(),
                value: gamma.clone(),
            },
        ));
        query_set_gadget.0.insert((
            "c_denom".to_string(),
            LabeledPointVar {
                name: "gamma".to_string(),
                value: gamma.clone(),
            },
        ));
        query_set_gadget.0.insert((
            "inner_sumcheck".to_string(),
            LabeledPointVar {
                name: "gamma".to_string(),
                value: gamma.clone(),
            },
        ));
        query_set_gadget.0.insert((
            "vanishing_poly_h_alpha".to_string(),
            LabeledPointVar {
                name: "alpha".to_string(),
                value: alpha.clone(),
            },
        ));
        query_set_gadget.0.insert((
            "vanishing_poly_h_beta".to_string(),
            LabeledPointVar {
                name: "beta".to_string(),
                value: beta.clone(),
            },
        ));
        query_set_gadget.0.insert((
            "vanishing_poly_k_gamma".to_string(),
            LabeledPointVar {
                name: "gamma".to_string(),
                value: gamma.clone(),
            },
        ));

        let mut evaluations_gadget = EvaluationsVar::<TargetField, BaseField> { 0: HashMap::new() };

        let zero = NonNativeFieldVar::<TargetField, BaseField>::zero(cs.ns(|| "nonnative_zero"))?;

        evaluations_gadget.0.insert(
            LabeledPointVar {
                name: "g_1".to_string(),
                value: beta.clone(),
            },
            (*proof.evaluations.get("g_1").unwrap()).clone(),
        );
        evaluations_gadget.0.insert(
            LabeledPointVar {
                name: "z_b".to_string(),
                value: beta.clone(),
            },
            (*proof.evaluations.get("z_b").unwrap()).clone(),
        );
        evaluations_gadget.0.insert(
            LabeledPointVar {
                name: "t".to_string(),
                value: beta.clone(),
            },
            (*proof.evaluations.get("t").unwrap()).clone(),
        );
        evaluations_gadget.0.insert(
            LabeledPointVar {
                name: "outer_sumcheck".to_string(),
                value: beta.clone(),
            },
            zero.clone(),
        );
        evaluations_gadget.0.insert(
            LabeledPointVar {
                name: "g_2".to_string(),
                value: gamma.clone(),
            },
            (*proof.evaluations.get("g_2").unwrap()).clone(),
        );
        evaluations_gadget.0.insert(
            LabeledPointVar {
                name: "a_denom".to_string(),
                value: gamma.clone(),
            },
            (*proof.evaluations.get("a_denom").unwrap()).clone(),
        );
        evaluations_gadget.0.insert(
            LabeledPointVar {
                name: "b_denom".to_string(),
                value: gamma.clone(),
            },
            (*proof.evaluations.get("b_denom").unwrap()).clone(),
        );
        evaluations_gadget.0.insert(
            LabeledPointVar {
                name: "c_denom".to_string(),
                value: gamma.clone(),
            },
            (*proof.evaluations.get("c_denom").unwrap()).clone(),
        );
        evaluations_gadget.0.insert(
            LabeledPointVar {
                name: "inner_sumcheck".to_string(),
                value: gamma.clone(),
            },
            zero,
        );
        evaluations_gadget.0.insert(
            LabeledPointVar {
                name: "vanishing_poly_h_alpha".to_string(),
                value: alpha.clone(),
            },
            (*proof.evaluations.get("vanishing_poly_h_alpha").unwrap()).clone(),
        );
        evaluations_gadget.0.insert(
            LabeledPointVar {
                name: "vanishing_poly_h_beta".to_string(),
                value: beta.clone(),
            },
            (*proof.evaluations.get("vanishing_poly_h_beta").unwrap()).clone(),
        );
        evaluations_gadget.0.insert(
            LabeledPointVar {
                name: "vanishing_poly_k_gamma".to_string(),
                value: gamma.clone(),
            },
            (*proof.evaluations.get("vanishing_poly_k_gamma").unwrap()).clone(),
        );

        let mut comms = vec![];

        const INDEX_LABELS: [&str; 14] = [
            "a_row",
            "a_col",
            "a_val",
            "a_row_col",
            "b_row",
            "b_col",
            "b_val",
            "b_row_col",
            "c_row",
            "c_col",
            "c_val",
            "c_row_col",
            "vanishing_poly_h",
            "vanishing_poly_k",
        ];

        // 14 comms for gamma from the index_vk
        for (comm, label) in index_pvk.prepared_index_comms.iter().zip(INDEX_LABELS.iter()) {
            comms.push(PCG::create_prepared_labeled_commitment(
                label.to_string(),
                comm.clone(),
                None,
            ));
        }

        // 4 comms for beta from the round 1
        const PROOF_1_LABELS: [&str; 4] = ["w", "z_a", "z_b", "mask_poly"];
        for (comm, label) in proof.commitments[0].iter().zip(PROOF_1_LABELS.iter()) {
            let prepared_comm = PCG::PreparedCommitmentVar::prepare(comm)?;
            comms.push(PCG::create_prepared_labeled_commitment(
                label.to_string(),
                prepared_comm,
                None,
            ));
        }

        let h_minus_2 = index_pvk
            .domain_h_size_gadget
            .clone()
            .sub_constant(cs.ns(|| "domain_h_minus_2"), &BaseField::from(2u128))?;

        // 3 comms for beta from the round 2
        const PROOF_2_LABELS: [&str; 3] = ["t", "g_1", "h_1"];
        let proof_2_bounds = [None, Some(h_minus_2), None];
        for ((comm, label), bound) in proof.commitments[1]
            .iter()
            .zip(PROOF_2_LABELS.iter())
            .zip(proof_2_bounds.iter())
        {
            let prepared_comm = PCG::PreparedCommitmentVar::prepare(comm)?;
            comms.push(PCG::create_prepared_labeled_commitment(
                label.to_string(),
                prepared_comm,
                (*bound).clone(),
            ));
        }

        let k_minus_2 = index_pvk
            .domain_k_size_gadget
            .sub_constant(cs.ns(|| "domain_k_minus_2"), &BaseField::from(2u128))?;

        // 2 comms for gamma from the round 3
        const PROOF_3_LABELS: [&str; 2] = ["g_2", "h_2"];
        let proof_3_bounds = [Some(k_minus_2), None];
        for ((comm, label), bound) in proof.commitments[2]
            .iter()
            .zip(PROOF_3_LABELS.iter())
            .zip(proof_3_bounds.into_iter())
        {
            let prepared_comm = PCG::PreparedCommitmentVar::prepare(comm)?;
            comms.push(PCG::create_prepared_labeled_commitment(
                label.to_string(),
                prepared_comm,
                *bound,
            ));
        }

        // For commitments; and combined commitments (degree bounds); and combined commitments again.
        let num_opening_challenges = 7;

        // Combined commitments.
        let num_batching_rands = 2;

        Ok((
            num_opening_challenges,
            num_batching_rands,
            comms,
            query_set_gadget,
            evaluations_gadget,
        ))
    }
}
