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
    constraints::{
        ahp::AHPForR1CS,
        data_structures::{CircuitVerifyingKeyVar, PreparedCircuitVerifyingKeyVar, ProofVar},
    },
    fiat_shamir::{constraints::FiatShamirRngVar, FiatShamirRng},
    marlin::MarlinError,
    PhantomData,
};
use snarkvm_fields::PrimeField;
use snarkvm_gadgets::traits::{
    fields::{FieldGadget, ToConstraintFieldGadget},
    utilities::boolean::Boolean,
};
use snarkvm_nonnative::{params::OptimizationType, NonNativeFieldVar};
use snarkvm_polycommit::{
    constraints::{PCCheckRandomDataVar, PCCheckVar},
    PolynomialCommitment,
};
use snarkvm_r1cs::ConstraintSystem;

/// The Marlin verification gadget.
pub struct MarlinVerificationGadget<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
>(
    PhantomData<TargetField>,
    PhantomData<BaseField>,
    PhantomData<PC>,
    PhantomData<PCG>,
);

impl<TargetField, BaseField, PC, PCG> MarlinVerificationGadget<TargetField, BaseField, PC, PCG>
where
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
    PCG::VerifierKeyVar: ToConstraintFieldGadget<BaseField>,
    PCG::CommitmentVar: ToConstraintFieldGadget<BaseField>,
{
    /// The encoding of the protocol name for use as seed.
    pub const PROTOCOL_NAME: &'static [u8] = b"MARLIN-2019";

    /// Verify with an established hashchain initial state.
    pub fn prepared_verify<
        CS: ConstraintSystem<BaseField>,
        PR: FiatShamirRng<TargetField, BaseField>,
        R: FiatShamirRngVar<TargetField, BaseField, PR>,
    >(
        mut cs: CS,
        prepared_verifying_key: &PreparedCircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG, PR, R>,
        public_input: &[NonNativeFieldVar<TargetField, BaseField>],
        proof: &ProofVar<TargetField, BaseField, PC, PCG>,
    ) -> Result<Boolean, MarlinError<PC::Error>> {
        let mut fs_rng = prepared_verifying_key.fs_rng.clone();

        eprintln!("before AHP: constraints: {}", cs.num_constraints());

        fs_rng.absorb_nonnative_field_elements(
            cs.ns(|| "initial_absorb_nonnative_field_elements"),
            &public_input,
            OptimizationType::Weight,
        )?;

        let (_, verifier_state) = AHPForR1CS::<TargetField, BaseField, PC, PCG>::verifier_first_round(
            cs.ns(|| "verifier_first_round"),
            prepared_verifying_key.domain_h_size,
            prepared_verifying_key.domain_k_size,
            &mut fs_rng,
            &proof.commitments[0],
            &proof.prover_messages[0].field_elements,
        )?;

        let (_, verifier_state) = AHPForR1CS::<TargetField, BaseField, PC, PCG>::verifier_second_round(
            cs.ns(|| "verifier_second_round"),
            verifier_state,
            &mut fs_rng,
            &proof.commitments[1],
            &proof.prover_messages[1].field_elements,
        )?;

        let verifier_state = AHPForR1CS::<TargetField, BaseField, PC, PCG>::verifier_third_round(
            cs.ns(|| "verifier_third_round"),
            verifier_state,
            &mut fs_rng,
            &proof.commitments[2],
            &proof.prover_messages[2].field_elements,
        )?;

        let mut formatted_public_input = vec![NonNativeFieldVar::one(cs.ns(|| "nonnative_one"))?];
        for elem in public_input.iter().cloned() {
            formatted_public_input.push(elem);
        }

        let lc = AHPForR1CS::<TargetField, BaseField, PC, PCG>::verifier_decision(
            cs.ns(|| "verifier_decision"),
            &formatted_public_input,
            &proof.evaluations,
            verifier_state.clone(),
            &prepared_verifying_key.domain_k_size_gadget,
        )?;

        let (num_opening_challenges, num_batching_rands, comm, query_set, evaluations) =
            AHPForR1CS::<TargetField, BaseField, PC, PCG>::verifier_comm_query_eval_set(
                cs.ns(|| "verifier_comm_query_eval_set"),
                &prepared_verifying_key,
                &proof,
                &verifier_state,
            )?;

        let mut evaluations_labels = Vec::<(String, NonNativeFieldVar<TargetField, BaseField>)>::new();
        for q in query_set.0.iter().cloned() {
            evaluations_labels.push((q.0.clone(), (q.1).value.clone()));
        }
        evaluations_labels.sort_by(|a, b| a.0.cmp(&b.0));

        let mut evals_vec: Vec<NonNativeFieldVar<TargetField, BaseField>> = Vec::new();
        for (label, point) in evaluations_labels.iter() {
            if label != "outer_sumcheck" && label != "inner_sumcheck" {
                evals_vec.push(evaluations.get_lc_eval(label, point).unwrap());
            }
        }

        fs_rng.absorb_nonnative_field_elements(
            cs.ns(|| "final_absorb_nonnative_field_elements"),
            &evals_vec,
            OptimizationType::Weight,
        )?;

        let (opening_challenges, opening_challenges_bits) = fs_rng.squeeze_128_bits_field_elements_and_bits(
            cs.ns(|| "opening_squeeze_128_bits_field_elements_and_bits"),
            num_opening_challenges,
        )?;
        let (batching_rands, batching_rands_bits) = fs_rng.squeeze_128_bits_field_elements_and_bits(
            cs.ns(|| "batching_squeeze_128_bits_field_elements_and_bits"),
            num_batching_rands,
        )?;

        eprintln!("before PC checks: constraints: {}", cs.num_constraints());

        let rand_data = PCCheckRandomDataVar::<TargetField, BaseField> {
            opening_challenges,
            opening_challenges_bits,
            batching_rands,
            batching_rands_bits,
        };

        Ok(PCG::prepared_check_combinations(
            cs.ns(|| "prepared_check_combinations"),
            &prepared_verifying_key.prepared_verifier_key,
            &lc,
            &comm,
            &query_set,
            &evaluations,
            &proof.pc_batch_proof,
            &rand_data,
        )?)
    }

    /// Verify with an established hashchain initial state.
    pub fn verify<
        CS: ConstraintSystem<BaseField>,
        PR: FiatShamirRng<TargetField, BaseField>,
        R: FiatShamirRngVar<TargetField, BaseField, PR>,
    >(
        mut cs: CS,
        verifying_key: &CircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG>,
        public_input: &[NonNativeFieldVar<TargetField, BaseField>],
        proof: &ProofVar<TargetField, BaseField, PC, PCG>,
    ) -> Result<Boolean, MarlinError<PC::Error>> {
        let prepared_verifying_key = PreparedCircuitVerifyingKeyVar::<TargetField, BaseField, PC, PCG, PR, R>::prepare(
            cs.ns(|| "prepare"),
            &verifying_key,
        )?;
        Self::prepared_verify(
            cs.ns(|| "prepared_verify"),
            &prepared_verifying_key,
            public_input,
            proof,
        )
    }
}
