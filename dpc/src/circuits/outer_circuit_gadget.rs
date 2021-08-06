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

use crate::{OuterPrivateVariables, OuterPublicVariables, Parameters};
use snarkvm_fields::ToConstraintField;
use snarkvm_gadgets::{
    algorithms::merkle_tree::MerklePathGadget,
    bits::ToBytesGadget,
    traits::{
        algorithms::{CRHGadget, CommitmentGadget, SNARKVerifierGadget},
        alloc::AllocGadget,
        eq::EqGadget,
    },
    MergeGadget,
    ToBitsLEGadget,
    ToConstraintFieldGadget,
};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

use itertools::Itertools;

fn alloc_inner_snark_field_element<
    C: Parameters,
    V: ToConstraintField<C::InnerScalarField>,
    CS: ConstraintSystem<C::OuterScalarField>,
>(
    cs: &mut CS,
    var: &V,
    name: &str,
) -> Result<<C::InnerSNARKGadget as SNARKVerifierGadget<C::InnerSNARK>>::InputGadget, SynthesisError> {
    let field_elements = var.to_field_elements().map_err(|_| SynthesisError::AssignmentMissing)?;
    <C::InnerSNARKGadget as SNARKVerifierGadget<_>>::InputGadget::alloc(
        cs.ns(|| format!("alloc_field_element_{}", name)),
        || Ok(field_elements),
    )
}

fn alloc_inner_snark_input_field_element<
    'a,
    C: Parameters,
    V: ToConstraintField<C::InnerScalarField>,
    CS: ConstraintSystem<C::OuterScalarField>,
>(
    cs: &mut CS,
    var: &V,
    name: &str,
) -> Result<<C::InnerSNARKGadget as SNARKVerifierGadget<C::InnerSNARK>>::InputGadget, SynthesisError> {
    let field_elements = var.to_field_elements().map_err(|_| SynthesisError::AssignmentMissing)?;
    // allocate the field elements one by one
    let mut input_gadgets = Vec::with_capacity(field_elements.len());
    for (j, field_element) in field_elements.iter().enumerate() {
        input_gadgets.push(
            <C::InnerSNARKGadget as SNARKVerifierGadget<_>>::InputGadget::alloc_input(
                cs.ns(|| format!("alloc_input_field_element_{}_{}", name, j)),
                || Ok(vec![(*field_element).clone()]),
            )?,
        )
    }
    <C::InnerSNARKGadget as SNARKVerifierGadget<C::InnerSNARK>>::InputGadget::merge_many(
        cs.ns(|| format!("alloc_input_field_element_{}_merge", name)),
        &input_gadgets,
    )
}

fn alloc_program_snark_field_element<
    C: Parameters,
    V: ToConstraintField<C::InnerScalarField>,
    CS: ConstraintSystem<C::OuterScalarField>,
>(
    cs: &mut CS,
    var: &V,
    name: &str,
) -> Result<<C::ProgramSNARKGadget as SNARKVerifierGadget<C::ProgramSNARK>>::InputGadget, SynthesisError> {
    let field_elements = var.to_field_elements().map_err(|_| SynthesisError::AssignmentMissing)?;
    <C::ProgramSNARKGadget as SNARKVerifierGadget<_>>::InputGadget::alloc(
        cs.ns(|| format!("alloc_field_element_{}", name)),
        || Ok(field_elements),
    )
}

pub fn execute_outer_circuit<C: Parameters, CS: ConstraintSystem<C::OuterScalarField>>(
    cs: &mut CS,
    public: &OuterPublicVariables<C>,
    private: &OuterPrivateVariables<C>,
) -> Result<(), SynthesisError> {
    // Access the outer public variables.
    let OuterPublicVariables {
        inner_public_variables: inner_public,
        inner_circuit_id,
    } = public;

    // In the outer circuit, these two variables must be allocated as witness,
    // as they are not included in the transaction.
    debug_assert!(inner_public.program_commitment.is_none());
    debug_assert!(inner_public.local_data_root.is_none());

    // ************************************************************************
    // Declare public parameters.
    // ************************************************************************

    let program_id_commitment_parameters =
        C::ProgramCommitmentGadget::alloc_constant(&mut cs.ns(|| "Declare program_id_commitment_parameters"), || {
            Ok(C::program_commitment_scheme().clone())
        })?;

    let program_circuit_id_crh = C::ProgramCircuitIDCRHGadget::alloc_constant(
        &mut cs.ns(|| "Declare program_circuit_id_crh_parameters"),
        || Ok(C::program_circuit_id_crh().clone()),
    )?;

    let inner_circuit_id_crh =
        C::InnerCircuitIDCRHGadget::alloc_constant(&mut cs.ns(|| "Declare inner_circuit_id_crh_parameters"), || {
            Ok(C::inner_circuit_id_crh().clone())
        })?;

    // ************************************************************************
    // Construct the inner circuit input.
    // ************************************************************************

    // Declare inner circuit public variables as inner circuit field elements

    let ledger_digest_fe =
        alloc_inner_snark_input_field_element::<C, _, _>(cs, &inner_public.ledger_digest, "ledger digest")?;

    let serial_number_fe = {
        let mut serial_number_fe_vec = Vec::with_capacity(inner_public.kernel.serial_numbers.len());
        for (index, sn) in inner_public.kernel.serial_numbers.iter().enumerate() {
            let this_serial_number_fe =
                alloc_inner_snark_input_field_element::<C, _, _>(cs, sn, &format!("serial number {}", index))?;

            serial_number_fe_vec.push(this_serial_number_fe);
        }

        <C::InnerSNARKGadget as SNARKVerifierGadget<_>>::InputGadget::merge_many(
            cs.ns(|| "serial number"),
            &serial_number_fe_vec,
        )?
    };

    let commitment_and_encrypted_record_hash_fe = {
        let mut commitment_and_encrypted_record_hash_fe_vec =
            Vec::with_capacity(inner_public.kernel.commitments.len() * C::NUM_OUTPUT_RECORDS);
        for (index, (cm, encrypted_record_hash)) in inner_public
            .kernel
            .commitments
            .iter()
            .zip_eq(inner_public.encrypted_record_hashes.iter())
            .enumerate()
        {
            let commitment_fe =
                alloc_inner_snark_input_field_element::<C, _, _>(cs, cm, &format!("commitment {}", index))?;
            let encrypted_record_hash_fe = alloc_inner_snark_input_field_element::<C, _, _>(
                cs,
                encrypted_record_hash,
                &format!("encrypted_record_hash {}", index),
            )?;

            commitment_and_encrypted_record_hash_fe_vec.push(commitment_fe);
            commitment_and_encrypted_record_hash_fe_vec.push(encrypted_record_hash_fe);
        }

        <C::InnerSNARKGadget as SNARKVerifierGadget<_>>::InputGadget::merge_many(
            cs.ns(|| "commitment_and_encrypted_record_hash"),
            &commitment_and_encrypted_record_hash_fe_vec,
        )?
    };

    let memo_fe = alloc_inner_snark_input_field_element::<C, _, _>(cs, &inner_public.kernel.memo, "memo")?;

    let network_id_fe =
        alloc_inner_snark_input_field_element::<C, _, _>(cs, &[inner_public.kernel.network_id], "network id")?;

    let value_balance_fe = alloc_inner_snark_input_field_element::<C, _, _>(
        cs,
        &inner_public.kernel.value_balance.0.to_le_bytes(),
        "value balance",
    )?;

    let program_commitment_fe =
        alloc_inner_snark_field_element::<C, _, _>(cs, &private.program_commitment, "program commitment")?;

    let local_data_root_fe_inner_snark =
        alloc_inner_snark_field_element::<C, _, _>(cs, &private.local_data_root, "local data root inner snark")?;

    let local_data_root_fe_program_snark =
        alloc_program_snark_field_element::<C, _, _>(cs, &private.local_data_root, "local data root program snark")?;

    {
        // Construct inner snark input as bits
        let local_data_root_input_inner_snark_bits =
            local_data_root_fe_inner_snark.to_bits_le(cs.ns(|| "local data root inner snark to bits"))?;
        let local_data_root_input_program_snark_bits =
            local_data_root_fe_program_snark.to_bits_le(cs.ns(|| "local data root program snark to bits"))?;
        local_data_root_input_inner_snark_bits.enforce_equal(
            cs.ns(|| "local data root equality"),
            &local_data_root_input_program_snark_bits,
        )?;
    }

    let inner_snark_input =
        <C::InnerSNARKGadget as SNARKVerifierGadget<_>>::InputGadget::merge_many(cs.ns(|| "inner_snark_input"), &[
            ledger_digest_fe,
            serial_number_fe,
            commitment_and_encrypted_record_hash_fe,
            program_commitment_fe,
            memo_fe,
            network_id_fe,
            local_data_root_fe_inner_snark,
            value_balance_fe,
        ])?;

    // ************************************************************************
    // Verify the inner circuit proof.
    // ************************************************************************

    let inner_snark_vk = <C::InnerSNARKGadget as SNARKVerifierGadget<_>>::VerificationKeyGadget::alloc(
        &mut cs.ns(|| "Allocate inner circuit verifying key"),
        || Ok(&private.inner_snark_vk),
    )?;

    let inner_snark_proof = <C::InnerSNARKGadget as SNARKVerifierGadget<_>>::ProofGadget::alloc(
        &mut cs.ns(|| "Allocate inner circuit proof"),
        || Ok(&private.inner_snark_proof),
    )?;

    C::InnerSNARKGadget::check_verify(
        &mut cs.ns(|| "Check that proof is satisfied"),
        &inner_snark_vk,
        &inner_snark_input,
        &inner_snark_proof,
    )?;

    // ************************************************************************
    // Verify each circuit exist in declared program and verify their proofs.
    // ************************************************************************

    let mut program_ids = Vec::with_capacity(C::NUM_TOTAL_RECORDS);
    for (index, input) in private.program_proofs.iter().enumerate().take(C::NUM_TOTAL_RECORDS) {
        let cs = &mut cs.ns(|| format!("Check program for record {}", index));

        let program_circuit_proof = <C::ProgramSNARKGadget as SNARKVerifierGadget<_>>::ProofGadget::alloc(
            &mut cs.ns(|| "Allocate program circuit proof"),
            || Ok(&input.proof),
        )?;

        let program_circuit_verifying_key =
            <C::ProgramSNARKGadget as SNARKVerifierGadget<_>>::VerificationKeyGadget::alloc(
                &mut cs.ns(|| "Allocate program circuit verifying key"),
                || Ok(&input.verifying_key),
            )?;

        let program_circuit_verifying_key_field_elements = program_circuit_verifying_key
            .to_constraint_field(cs.ns(|| "alloc_program_circuit_verifying_key_field_elements"))?;

        let claimed_circuit_id = program_circuit_id_crh.check_evaluation_gadget_on_field_elements(
            &mut cs.ns(|| "Compute circuit ID"),
            program_circuit_verifying_key_field_elements,
        )?;

        let claimed_circuit_id_bytes =
            claimed_circuit_id.to_bytes(&mut cs.ns(|| "Convert death circuit ID to bytes"))?;

        let death_program_merkle_path_gadget = MerklePathGadget::<_, C::ProgramCircuitIDCRHGadget, _>::alloc(
            &mut cs.ns(|| "Declare program path for circuit"),
            || Ok(&input.program_path),
        )?;

        let claimed_program_id = death_program_merkle_path_gadget.calculate_root(
            &mut cs.ns(|| "calculate_program_id"),
            &program_circuit_id_crh,
            claimed_circuit_id_bytes,
        )?;

        let claimed_program_id_bytes =
            claimed_program_id.to_bytes(&mut cs.ns(|| "Convert program ID root to bytes"))?;

        program_ids.push(claimed_program_id_bytes);

        let position_fe = <C::ProgramSNARKGadget as SNARKVerifierGadget<_>>::InputGadget::alloc_constant(
            &mut cs.ns(|| "Allocate position"),
            || Ok(vec![C::InnerScalarField::from(index as u128)]),
        )?;
        let program_input = position_fe.merge(cs.ns(|| "Allocate program input"), &local_data_root_fe_program_snark)?;

        C::ProgramSNARKGadget::check_verify(
            &mut cs.ns(|| "Check that proof is satisfied"),
            &program_circuit_verifying_key,
            &program_input,
            &program_circuit_proof,
        )?;
    }

    // ********************************************************************

    // ********************************************************************
    // Check that the program commitment is derived correctly.
    // ********************************************************************
    {
        let commitment_cs = &mut cs.ns(|| "Check that program commitment is well-formed");

        let mut input = Vec::new();
        for id in program_ids.iter().take(C::NUM_TOTAL_RECORDS) {
            input.extend_from_slice(&id);
        }

        let given_commitment_randomness =
            <C::ProgramCommitmentGadget as CommitmentGadget<_, C::OuterScalarField>>::RandomnessGadget::alloc(
                &mut commitment_cs.ns(|| "Commitment randomness"),
                || Ok(&private.program_randomness),
            )?;

        let given_commitment =
            <C::ProgramCommitmentGadget as CommitmentGadget<_, C::OuterScalarField>>::OutputGadget::alloc(
                &mut commitment_cs.ns(|| "Commitment output"),
                || Ok(&private.program_commitment),
            )?;

        let candidate_commitment = program_id_commitment_parameters.check_commitment_gadget(
            &mut commitment_cs.ns(|| "Compute commitment"),
            &input,
            &given_commitment_randomness,
        )?;

        candidate_commitment.enforce_equal(
            &mut commitment_cs.ns(|| "Check that declared and computed commitments are equal"),
            &given_commitment,
        )?;
    }

    // ********************************************************************

    // ********************************************************************
    // Check that the inner circuit ID is derived correctly.
    // ********************************************************************

    let inner_snark_vk_field_elements =
        inner_snark_vk.to_constraint_field(&mut cs.ns(|| "Convert inner snark vk to field elements"))?;

    let given_inner_circuit_id =
        <C::InnerCircuitIDCRHGadget as CRHGadget<_, C::OuterScalarField>>::OutputGadget::alloc_input(
            &mut cs.ns(|| "Inner circuit ID"),
            || Ok(inner_circuit_id),
        )?;

    let candidate_inner_circuit_id = inner_circuit_id_crh.check_evaluation_gadget_on_field_elements(
        &mut cs.ns(|| "Compute inner circuit ID"),
        inner_snark_vk_field_elements,
    )?;

    candidate_inner_circuit_id.enforce_equal(
        &mut cs.ns(|| "Check that declared and computed inner circuit IDs are equal"),
        &given_inner_circuit_id,
    )?;

    Ok(())
}
