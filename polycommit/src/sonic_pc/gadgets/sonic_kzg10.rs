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

use core::{convert::TryInto, marker::PhantomData};

use snarkvm_curves::PairingEngine;
use snarkvm_gadgets::{
    bits::{Boolean, ToBitsLEGadget},
    fields::FpGadget,
    nonnative::{NonNativeFieldMulResultVar, NonNativeFieldVar},
    traits::{
        curves::{GroupGadget, PairingGadget},
        eq::EqGadget,
        fields::FieldGadget,
        select::CondSelectGadget,
    },
};
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

use crate::{
    sonic_pc::{
        prepared_labeled_commitment::PreparedLabeledCommitmentVar,
        proof::{batch_lc_proof::BatchLCProofVar, ProofVar},
        verifier_key::{prepared_verifier_key::PreparedVerifierKeyVar, VerifierKeyVar},
        CommitmentVar,
        LabeledCommitmentVar,
        PreparedCommitmentVar,
        SonicKZG10,
    },
    BTreeMap,
    BTreeSet,
    EvaluationsVar,
    LabeledPointVar,
    LinearCombinationCoeffVar,
    LinearCombinationVar,
    PCCheckRandomDataVar,
    PCCheckVar,
    QuerySetVar,
    String,
    Vec,
};

/// Gadget for each entry for the linear combination
#[derive(Derivative)]
#[derivative(Clone(bound = "TargetCurve: PairingEngine,
        BaseCurve: PairingEngine,
        PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>"))]
pub struct LCInfoEntry<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
{
    pub coeff: Option<NonNativeFieldVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>>,
    pub degree_bound: Option<FpGadget<<BaseCurve as PairingEngine>::Fr>>,
    pub prepared_comm: PreparedCommitmentVar<TargetCurve, BaseCurve, PG>,
    pub negate: bool,
}

impl<TargetCurve, BaseCurve, PG> LCInfoEntry<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
{
    pub fn new(
        coeff: &Option<NonNativeFieldVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>>,
        degree_bound: &Option<FpGadget<<BaseCurve as PairingEngine>::Fr>>,
        prepared_comm: &PreparedCommitmentVar<TargetCurve, BaseCurve, PG>,
        negate: bool,
    ) -> Self {
        Self { coeff: coeff.clone(), degree_bound: degree_bound.clone(), prepared_comm: prepared_comm.clone(), negate }
    }
}

/// Gadget for the Sonic-KZG10 polynomial commitment verifier.
pub struct SonicKZG10Gadget<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
{
    _target_curve: PhantomData<TargetCurve>,
    _base_curve: PhantomData<BaseCurve>,
    _pairing_gadget: PhantomData<PG>,
}

impl<TargetCurve, BaseCurve, PG> Clone for SonicKZG10Gadget<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
{
    fn clone(&self) -> Self {
        Self { _target_curve: PhantomData, _base_curve: PhantomData, _pairing_gadget: PhantomData }
    }
}

impl<TargetCurve, BaseCurve, PG> SonicKZG10Gadget<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine<Fq = <BaseCurve as PairingEngine>::Fr>,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
{
    #[allow(clippy::type_complexity, clippy::too_many_arguments)]
    fn prepared_batch_check_evaluations<CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>>(
        mut cs: CS,
        prepared_verification_key: &<Self as PCCheckVar<
            <TargetCurve as PairingEngine>::Fr,
            SonicKZG10<TargetCurve>,
            <BaseCurve as PairingEngine>::Fr,
        >>::PreparedVerifierKeyVar,
        lc_info: &[(String, Vec<LCInfoEntry<TargetCurve, BaseCurve, PG>>)],
        query_set: &QuerySetVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>,
        evaluations: &EvaluationsVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>,
        proofs: &[<Self as PCCheckVar<
            <TargetCurve as PairingEngine>::Fr,
            SonicKZG10<TargetCurve>,
            <BaseCurve as PairingEngine>::Fr,
        >>::ProofVar],
        opening_challenges: &[NonNativeFieldVar<
            <TargetCurve as PairingEngine>::Fr,
            <BaseCurve as PairingEngine>::Fr,
        >],
        opening_challenges_bits: &[Vec<Boolean>],
        batching_rands: &[NonNativeFieldVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>],
        batching_rands_bits: &[Vec<Boolean>],
    ) -> Result<Boolean, SynthesisError> {
        let mut batching_rands = batching_rands.to_vec();
        let mut batching_rands_bits = batching_rands_bits.to_vec();

        // Organize all the commitment linear combinations.
        //
        // The string is the name of the linear combination.
        // The vector is a list of commitments to polynomials (referenced by names), the corresponding coefficient, and
        let commitment_lcs: BTreeMap<String, (String, Vec<LCInfoEntry<TargetCurve, BaseCurve, PG>>)> =
            lc_info.iter().map(|c| (c.0.clone(), c.clone())).collect();

        // Organize a map from queries to linear combinations (referenced by names).
        let mut query_to_labels_map: BTreeMap<
            String,
            (
                NonNativeFieldVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>,
                BTreeSet<&String>,
            ),
        > = BTreeMap::new();

        // Sort the query based on the names of the points.
        let mut sorted_query_set_gadgets: Vec<_> = query_set.0.iter().collect();
        sorted_query_set_gadgets.sort_by(|a, b| a.0.cmp(&b.0));

        // Group the queries on the same point.
        for (label, point) in sorted_query_set_gadgets.iter() {
            let labels =
                query_to_labels_map.entry(point.name.clone()).or_insert((point.value.clone(), BTreeSet::new()));
            labels.1.insert(label);
        }

        if cfg!(debug_assertions) {
            eprintln!("before PC combining commitments: constraints: {}", cs.num_constraints());
        }

        let zero = PG::G1Gadget::zero(cs.ns(|| "g1_zero"))?;

        // Accumulate commitments and evaluations for each query.
        //
        // For clarify, we separate the cases when there is a degree bound and when there is no.
        //
        let mut combined_non_degree_bound_comms = Vec::new();
        let mut combined_queries = Vec::new();
        let mut combined_evals = Vec::new();

        let mut combined_degree_bound_comms = Vec::new();
        let mut combined_degree_bound_shift_powers = Vec::new();

        // Now, for each point, go over all the linear combinations using this point
        for (i, (_, (point, labels))) in query_to_labels_map.into_iter().enumerate() {
            // Initialize the vectors to store the combination decisions.
            let mut comms_to_combine = Vec::<Vec<LCInfoEntry<TargetCurve, BaseCurve, PG>>>::with_capacity(labels.len());
            let mut values_to_combine = Vec::with_capacity(labels.len());

            // Go through all the labels
            for label in labels.into_iter() {
                let commitment_lc = commitment_lcs.get(label).unwrap().clone();

                let v_i = evaluations.0.get(&LabeledPointVar { name: label.clone(), value: point.clone() }).unwrap();

                comms_to_combine.push(commitment_lc.1.clone());
                values_to_combine.push(v_i.clone());
            }

            // Accumulate the commitments and evaluations corresponding to `query`.
            let mut combined_eval = NonNativeFieldMulResultVar::<
                <TargetCurve as PairingEngine>::Fr,
                <BaseCurve as PairingEngine>::Fr,
            >::zero();
            let mut combined_non_degree_bound_comm =
                PG::G1Gadget::zero(cs.ns(|| format!("non_degree_bound_comm_zero_{}", i)))?;
            let mut degree_bound_comms = Vec::<PG::G1Gadget>::new();
            let mut shift_powers = Vec::<PG::G2PreparedGadget>::new();

            for (j, (commitment_lcs, value)) in comms_to_combine.into_iter().zip(values_to_combine).enumerate() {
                let opening_challenges_counter = j;
                let challenge = opening_challenges[opening_challenges_counter].clone();
                let challenge_bits = opening_challenges_bits[opening_challenges_counter].clone();

                for (k, commitment_lc) in commitment_lcs.iter().enumerate() {
                    let LCInfoEntry { coeff, degree_bound, prepared_comm: comm, negate } = commitment_lc;

                    if coeff.is_none() {
                        // To combine the commitments, we multiply each by one of the random challenges, and sum.
                        let mut comm_times_challenge = PG::G1Gadget::zero(cs.ns(|| format!("zero_{}_{}_{}", i, j, k)))?;
                        {
                            for (l, (bit, base_power)) in
                                challenge_bits.iter().zip(comm.prepared_comm.iter()).enumerate()
                            {
                                let mut new_encoded = base_power.clone();
                                new_encoded = new_encoded.add(
                                    cs.ns(|| format!("new_encoded_plus_comm_times_challenge_{}_{}_{}_{}", i, j, k, l)),
                                    &comm_times_challenge,
                                )?;
                                comm_times_challenge = PG::G1Gadget::conditionally_select(
                                    cs.ns(|| format!("comm_times_challenge_cond_select_{}_{}_{}_{}", i, j, k, l)),
                                    bit,
                                    &new_encoded,
                                    &comm_times_challenge,
                                )?;
                            }
                        }

                        if negate.eq(&true) {
                            comm_times_challenge = comm_times_challenge
                                .negate(cs.ns(|| format!("negate_comm_times_challenge_{}_{}_{}", i, j, k)))?;
                        }

                        if let Some(degree_bound) = degree_bound {
                            degree_bound_comms.push(comm_times_challenge);
                            let shift_power = prepared_verification_key.get_prepared_shift_power(
                                cs.ns(|| format!("prepared_vk_get_shift_power_{}_{}_{}", i, j, k)),
                                degree_bound,
                            )?;
                            shift_powers.push(shift_power);
                        } else {
                            combined_non_degree_bound_comm = combined_non_degree_bound_comm.add(
                                cs.ns(|| format!("combined_comm_plus_comm_times_challenge_{}_{}_{}", i, j, k)),
                                &comm_times_challenge,
                            )?;
                        }
                    } else {
                        assert!(degree_bound.is_none());

                        let mut comm_times_challenge = PG::G1Gadget::zero(cs.ns(|| format!("zero_{}_{}_{}", i, j, k)))?;
                        let coeff = coeff.clone().unwrap();

                        let challenge_times_coeff =
                            challenge.mul(&mut cs.ns(|| format!("challenge_times_coeff_{}_{}_{}", i, j, k)), &coeff)?;

                        let challenge_times_coeff_bits = challenge_times_coeff
                            .to_bits_le(cs.ns(|| format!("challenge_times_coeff_to_bits_le_{}_{}_{}", i, j, k)))?;

                        {
                            for (l, (bit, base_power)) in
                                challenge_times_coeff_bits.iter().zip(&comm.prepared_comm).enumerate()
                            {
                                let mut new_encoded = comm_times_challenge.clone();
                                new_encoded = new_encoded.add(
                                    cs.ns(|| format!("new_encoded_add_base_power_{}_{}_{}_{}", i, j, k, l)),
                                    base_power,
                                )?;

                                comm_times_challenge = PG::G1Gadget::conditionally_select(
                                    cs.ns(|| format!("comm_times_challenge_cond_select_{}_{}_{}_{}", i, j, k, l)),
                                    bit,
                                    &new_encoded,
                                    &comm_times_challenge,
                                )?;
                            }
                        }

                        if negate.eq(&true) {
                            comm_times_challenge = comm_times_challenge
                                .negate(cs.ns(|| format!("comm_times_challenge_negate_{}_{}_{}", i, j, k)))?;
                        }

                        combined_non_degree_bound_comm = combined_non_degree_bound_comm.add(
                            &mut cs.ns(|| format!("combined_comm_add_comm_times_challenge_{}_{}_{}", i, j, k)),
                            &comm_times_challenge,
                        )?;
                    }
                }
                // Similarly, we add up the evaluations, multiplied with random challenges.
                let value_times_challenge_unreduced =
                    value.mul_without_reduce(cs.ns(|| format!("value_mul_without_reduce_{}_{}", i, j)), &challenge)?;

                combined_eval = combined_eval.add(
                    &mut cs.ns(|| format!("combined_eval_add_value_times_challenge_unreduced_{}_{}", i, j)),
                    &value_times_challenge_unreduced,
                )?;
            }

            let combined_eval_reduced = combined_eval.reduce(&mut cs.ns(|| format!("combined_eval_reduced_{}", i)))?;

            combined_queries.push(point.clone());
            combined_non_degree_bound_comms.push(combined_non_degree_bound_comm);
            combined_evals.push(combined_eval_reduced);

            combined_degree_bound_comms.push(degree_bound_comms);
            combined_degree_bound_shift_powers.push(shift_powers);
        }

        if cfg!(debug_assertions) {
            eprintln!("before PC batch check: constraints: {}", cs.num_constraints());
        }

        // Perform the batch check.
        {
            let mut total_c = PG::G1Gadget::zero(cs.ns(|| "zero_c"))?;
            let mut total_w = PG::G1Gadget::zero(cs.ns(|| "zero_w"))?;

            let mut g_multiplier = NonNativeFieldMulResultVar::<
                <TargetCurve as PairingEngine>::Fr,
                <BaseCurve as PairingEngine>::Fr,
            >::zero();
            let mut g_multiplier_reduced = NonNativeFieldVar::<
                <TargetCurve as PairingEngine>::Fr,
                <BaseCurve as PairingEngine>::Fr,
            >::zero(cs.ns(|| "zero_g_multiplier"))?;

            let mut gamma_g_multiplier = NonNativeFieldMulResultVar::<
                <TargetCurve as PairingEngine>::Fr,
                <BaseCurve as PairingEngine>::Fr,
            >::zero();
            let mut gamma_g_multiplier_reduced = NonNativeFieldVar::<
                <TargetCurve as PairingEngine>::Fr,
                <BaseCurve as PairingEngine>::Fr,
            >::zero(cs.ns(|| "zero_gamma_g_multiplier"))?;

            for (i, (((c, z), v), proof)) in
                combined_non_degree_bound_comms.iter().zip(combined_queries).zip(combined_evals).zip(proofs).enumerate()
            {
                let z_bits = z.to_bits_le(cs.ns(|| format!("z_bits_to_le_{}", i)))?;

                let w_times_z =
                    proof.w.mul_bits(cs.ns(|| format!("w_times_z_mul_bits_{}", i)), &zero, z_bits.into_iter())?;

                let mut c_plus_w_times_z = c.clone();
                c_plus_w_times_z =
                    c_plus_w_times_z.add(cs.ns(|| format!("c_plus_w_times_z_plus_w_times_z_{}", i)), &w_times_z)?;

                if i != 0 {
                    let randomizer = batching_rands.remove(0);
                    let randomizer_bits = batching_rands_bits.remove(0);

                    let randomizer_times_v =
                        randomizer.mul_without_reduce(cs.ns(|| format!("mul_without_reduce_{}", i)), &v)?;

                    g_multiplier = g_multiplier.add(
                        &mut cs.ns(|| format!("g_multiplier_plus_randomizer_times_v_{}", i)),
                        &randomizer_times_v,
                    )?;

                    if let Some(random_v) = &proof.random_v {
                        let randomizer_times_random_v = randomizer
                            .mul_without_reduce(cs.ns(|| format!("mul_without_reduce_{}_random_v", i)), random_v)?;

                        gamma_g_multiplier = gamma_g_multiplier.add(
                            &mut cs.ns(|| format!("gamma_g_multiplier_plus_randomizer_times_random_v_{}", i)),
                            &randomizer_times_random_v,
                        )?;
                    }

                    let c_times_randomizer = c_plus_w_times_z.mul_bits(
                        cs.ns(|| format!("c_plus_w_times_z_mul_bits{}", i)),
                        &zero,
                        randomizer_bits.clone().into_iter(),
                    )?;
                    let w_times_randomizer = proof.w.mul_bits(
                        cs.ns(|| format!("proof_w_mul_bits{}", i)),
                        &zero,
                        randomizer_bits.clone().into_iter(),
                    )?;

                    total_c = total_c
                        .add(&mut cs.ns(|| format!("total_c_plus_c_times_randomizer_{}", i)), &c_times_randomizer)?;
                    total_w = total_w
                        .add(&mut cs.ns(|| format!("total_w_plus_w_times_randomizer_{}", i)), &w_times_randomizer)?;

                    // Update those with degree bounds
                    for (j, elem) in combined_degree_bound_comms[i].iter_mut().enumerate() {
                        *elem = elem.mul_bits(
                            cs.ns(|| format!("degree_bound_comm_multiplied_by_randomizer_{}_{}", i, j)),
                            &zero,
                            randomizer_bits.clone().into_iter(),
                        )?;
                    }
                } else {
                    g_multiplier_reduced =
                        g_multiplier_reduced.add(&mut cs.ns(|| format!("g_multiplier_reduced_plus_v_{}", i)), &v)?;
                    if let Some(random_v) = &proof.random_v {
                        gamma_g_multiplier_reduced = gamma_g_multiplier_reduced.add(
                            &mut cs.ns(|| format!("gamma_g_multiplier_plus_randomizer_times_random_v_{}", i)),
                            random_v,
                        )?;
                    }
                    total_c = total_c
                        .add(&mut cs.ns(|| format!("total_c_plus_c_plus_w_times_z_{}", i)), &c_plus_w_times_z)?;
                    total_w = total_w.add(&mut cs.ns(|| format!("total_w_plus_proof_w{}", i)), &proof.w)?;
                }
            }

            // Prepare each input to the pairing.
            let (prepared_total_w, prepared_beta_h, prepared_total_c, prepared_h) = {
                let reduced = g_multiplier.reduce(&mut cs.ns(|| "g_multiplier_reduce_sum"))?;
                let g_multiplier_reduced = g_multiplier_reduced.add(&mut cs.ns(|| "g_multiplier_reduce"), &reduced)?;
                let g_multiplier_bits = g_multiplier_reduced.to_bits_le(&mut cs.ns(|| "g_multiplier_to_bits_le"))?;

                let gamma_g_multiplier_reduced = {
                    let reduced = gamma_g_multiplier.reduce(&mut cs.ns(|| "gamma_g_multiplier_reduce_sum"))?;
                    gamma_g_multiplier_reduced.add(&mut cs.ns(|| "gamma_g_multiplier_reduce"), &reduced)?
                };
                let gamma_g_multiplier_bits =
                    gamma_g_multiplier_reduced.to_bits_le(&mut cs.ns(|| "gamma_g_multiplier_to_bits_le"))?;

                let mut g_times_mul = PG::G1Gadget::zero(cs.ns(|| "g_times_mul_zero"))?;
                {
                    for (i, (bit, base_power)) in
                        g_multiplier_bits.iter().zip(&prepared_verification_key.prepared_g).enumerate()
                    {
                        let mut new_encoded = g_times_mul.clone();
                        new_encoded =
                            new_encoded.add(cs.ns(|| format!("new_encoded_plus_base_power_{}", i)), base_power)?;

                        g_times_mul = PG::G1Gadget::conditionally_select(
                            cs.ns(|| format!("g_times_mul_cond_select_{}", i)),
                            bit,
                            &new_encoded,
                            &g_times_mul,
                        )?;
                    }
                }

                let mut gamma_g_times_mul = PG::G1Gadget::zero(cs.ns(|| "gamma_g_times_mul_zero"))?;
                {
                    for (i, (bit, base_power)) in
                        gamma_g_multiplier_bits.iter().zip(&prepared_verification_key.prepared_gamma_g).enumerate()
                    {
                        let mut new_encoded = gamma_g_times_mul.clone();
                        new_encoded = new_encoded
                            .add(cs.ns(|| format!("new_encoded_plus_base_power_{}_gamma_g", i)), base_power)?;

                        gamma_g_times_mul = PG::G1Gadget::conditionally_select(
                            cs.ns(|| format!("gamma_g_times_mul_cond_select_{}", i)),
                            bit,
                            &new_encoded,
                            &gamma_g_times_mul,
                        )?;
                    }
                }

                total_c = total_c.sub(&mut cs.ns(|| "total_c_minus_g_times_mul"), &g_times_mul)?;
                total_c = total_c.sub(&mut cs.ns(|| "total_c_minus_gamma_g_times_mul"), &gamma_g_times_mul)?;
                total_w = total_w.negate(cs.ns(|| "total_w_negate"))?;

                let prepared_total_w = PG::prepare_g1(cs.ns(|| "prepared_total_w"), total_w)?;
                let prepared_beta_h = prepared_verification_key.prepared_beta_h.clone();
                let prepared_total_c = PG::prepare_g1(cs.ns(|| "prepared_total_c"), total_c)?;
                let prepared_h = prepared_verification_key.prepared_h.clone();

                (prepared_total_w, prepared_beta_h, prepared_total_c, prepared_h)
            };

            let mut pairing_left = Vec::new();
            let mut pairing_right = Vec::new();

            for (i, (randomized_comms, shift_powers)) in
                combined_degree_bound_comms.iter().zip(combined_degree_bound_shift_powers.iter()).enumerate()
            {
                let mut prepared_randomized_comms = Vec::with_capacity(randomized_comms.len());
                for (j, randomized_comm) in randomized_comms.iter().enumerate() {
                    prepared_randomized_comms.push(PG::prepare_g1(
                        cs.ns(|| format!("prepared_randomized_comm_with_degree_bound_{}_{}", i, j)),
                        randomized_comm.clone(),
                    )?);
                }

                pairing_left.extend_from_slice(&prepared_randomized_comms);
                pairing_right.extend_from_slice(shift_powers);
            }
            pairing_left.extend_from_slice(&[prepared_total_w, prepared_total_c]);
            pairing_right.extend_from_slice(&[prepared_beta_h, prepared_h]);

            let lhs = PG::product_of_pairings(
                cs.ns(|| "lhs_product_of_pairings"),
                pairing_left.as_slice(),
                pairing_right.as_slice(),
            )?;

            if cfg!(debug_assertions) {
                eprintln!("after PC batch check: constraints: {}", cs.num_constraints());
            }

            let rhs = &PG::GTGadget::one(cs.ns(|| "rhs"))?;
            lhs.is_eq(cs.ns(|| "lhs_is_eq_rhs"), rhs)
        }
    }
}

impl<TargetCurve, BaseCurve, PG>
    PCCheckVar<<TargetCurve as PairingEngine>::Fr, SonicKZG10<TargetCurve>, <BaseCurve as PairingEngine>::Fr>
    for SonicKZG10Gadget<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine<Fq = <BaseCurve as PairingEngine>::Fr>,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
{
    type BatchLCProofVar = BatchLCProofVar<TargetCurve, BaseCurve, PG>;
    type CommitmentVar = CommitmentVar<TargetCurve, BaseCurve, PG>;
    type LabeledCommitmentVar = LabeledCommitmentVar<TargetCurve, BaseCurve, PG>;
    type PreparedCommitmentVar = PreparedCommitmentVar<TargetCurve, BaseCurve, PG>;
    type PreparedLabeledCommitmentVar = PreparedLabeledCommitmentVar<TargetCurve, BaseCurve, PG>;
    type PreparedVerifierKeyVar = PreparedVerifierKeyVar<TargetCurve, BaseCurve, PG>;
    type ProofVar = ProofVar<TargetCurve, BaseCurve, PG>;
    type VerifierKeyVar = VerifierKeyVar<TargetCurve, BaseCurve, PG>;

    #[allow(clippy::type_complexity)]
    fn prepared_check_combinations<CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>>(
        mut cs: CS,
        prepared_verification_key: &Self::PreparedVerifierKeyVar,
        linear_combinations: &[LinearCombinationVar<
            <TargetCurve as PairingEngine>::Fr,
            <BaseCurve as PairingEngine>::Fr,
        >],
        prepared_commitments: &[Self::PreparedLabeledCommitmentVar],
        query_set: &QuerySetVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>,
        evaluations: &EvaluationsVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>,
        proof: &Self::BatchLCProofVar,
        rand_data: &PCCheckRandomDataVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>,
    ) -> Result<Boolean, SynthesisError> {
        let BatchLCProofVar { proofs, .. } = proof;

        let label_comm_map = prepared_commitments.iter().map(|c| (c.label.clone(), c)).collect::<BTreeMap<_, _>>();

        let mut lc_info = Vec::new();
        let mut evaluations = evaluations.clone();

        // For each linear combination, we sum up the relevant commitments, multiplied
        // with their corresponding coefficients; these combined commitments are then
        // the inputs to the normal batch check.
        for (i, lc) in linear_combinations.iter().enumerate() {
            let lc_label = lc.label.clone();
            let num_polys = lc.terms.len();

            let mut coeffs_and_comms = Vec::new();

            for (j, (coeff, label)) in lc.terms.iter().enumerate() {
                if label.is_one() {
                    for (label, ref mut eval) in evaluations.0.iter_mut() {
                        if label.name == lc_label {
                            match coeff.clone() {
                                LinearCombinationCoeffVar::One => {
                                    let one = NonNativeFieldVar::one(cs.ns(|| format!("coeff_one_{}_{}", i, j)))?;
                                    **eval = (**eval).sub(cs.ns(|| format!("eval_minus_one_{}_{}", i, j)), &one)?;
                                }
                                LinearCombinationCoeffVar::MinusOne => {
                                    let one = NonNativeFieldVar::one(cs.ns(|| format!("coeff_one_{}_{}", i, j)))?;
                                    **eval = (**eval).add(cs.ns(|| format!("eval_add_one_{}_{}", i, j)), &one)?;
                                }
                                LinearCombinationCoeffVar::Var(variable) => {
                                    **eval =
                                        (**eval).sub(cs.ns(|| format!("eval_minus_variable_{}_{}", i, j)), &variable)?
                                }
                            };
                        }
                    }
                } else {
                    let label: &String = label.try_into().unwrap();
                    let &cur_comm = label_comm_map.get(label).unwrap();
                    let negate = match coeff {
                        LinearCombinationCoeffVar::One | LinearCombinationCoeffVar::Var(_) => false,
                        LinearCombinationCoeffVar::MinusOne => true,
                    };

                    if num_polys == 1 && cur_comm.degree_bound.is_some() {
                        assert!(
                            *coeff == LinearCombinationCoeffVar::One,
                            "Coefficient must be one for degree-bounded equations"
                        );
                    } else if cur_comm.degree_bound.is_some() {
                        eprintln!(
                            "A commitment with a degree bound cannot be linearly combined with any other commitment."
                        );
                        return Err(SynthesisError::Unsatisfiable);
                    }

                    let coeff = match coeff {
                        LinearCombinationCoeffVar::One => None,
                        LinearCombinationCoeffVar::MinusOne => None,
                        LinearCombinationCoeffVar::Var(variable) => Some(variable.clone()),
                    };

                    coeffs_and_comms.push(LCInfoEntry::new(
                        &coeff,
                        &cur_comm.degree_bound,
                        &cur_comm.prepared_commitment,
                        negate,
                    ));
                }
            }

            lc_info.push((lc_label, coeffs_and_comms));
        }

        Self::prepared_batch_check_evaluations(
            cs,
            prepared_verification_key,
            lc_info.as_slice(),
            query_set,
            &evaluations,
            proofs,
            &rand_data.opening_challenges,
            &rand_data.opening_challenges_bits,
            &rand_data.batching_rands,
            &rand_data.batching_rands_bits,
        )
    }

    fn create_labeled_commitment(
        label: String,
        commitment: Self::CommitmentVar,
        degree_bound: Option<FpGadget<<BaseCurve as PairingEngine>::Fr>>,
    ) -> Self::LabeledCommitmentVar {
        Self::LabeledCommitmentVar { label, commitment, degree_bound }
    }

    fn create_prepared_labeled_commitment(
        label: String,
        prepared_commitment: Self::PreparedCommitmentVar,
        degree_bound: Option<FpGadget<<BaseCurve as PairingEngine>::Fr>>,
    ) -> Self::PreparedLabeledCommitmentVar {
        Self::PreparedLabeledCommitmentVar { label, prepared_commitment, degree_bound }
    }
}
