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

use crate::{testnet2::Testnet2Components, AleoAmount, Execution, Transaction, TransactionScheme};
use snarkvm_algorithms::{
    merkle_tree::MerkleTreeDigest,
    traits::{CommitmentScheme, SignatureScheme, CRH, SNARK},
};
use snarkvm_fields::ToConstraintField;
use snarkvm_gadgets::{
    bits::ToBytesGadget,
    integers::uint::UInt8,
    traits::{
        algorithms::{CRHGadget, CommitmentGadget, SNARKVerifierGadget},
        alloc::AllocGadget,
        eq::EqGadget,
        integers::integer::Integer,
    },
    ToConstraintFieldGadget,
};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};
use snarkvm_utilities::ToBytes;

use itertools::Itertools;

fn alloc_field_element_to_bytes<C: Testnet2Components, CS: ConstraintSystem<C::OuterScalarField>>(
    cs: &mut CS,
    field_elements: Vec<C::InnerScalarField>,
    name: &str,
) -> Result<Vec<Vec<UInt8>>, SynthesisError> {
    let mut fe_bytes = Vec::with_capacity(field_elements.len());
    for (index, field_element) in field_elements.iter().enumerate() {
        fe_bytes.push(UInt8::alloc_vec(
            cs.ns(|| format!("Allocate {} - index {} ", name, index)),
            &field_element
                .to_bytes_le()
                .map_err(|_| SynthesisError::AssignmentMissing)?,
        )?);
    }
    Ok(fe_bytes)
}

fn alloc_input_field_element_to_bytes<C: Testnet2Components, CS: ConstraintSystem<C::OuterScalarField>>(
    cs: &mut CS,
    field_elements: Vec<C::InnerScalarField>,
    name: &str,
) -> Result<Vec<Vec<UInt8>>, SynthesisError> {
    let mut fe_bytes = Vec::with_capacity(field_elements.len());
    for (index, field_element) in field_elements.iter().enumerate() {
        fe_bytes.push(UInt8::alloc_input_vec_le(
            cs.ns(|| format!("Allocate {} - index {} ", name, index)),
            &field_element
                .to_bytes_le()
                .map_err(|_| SynthesisError::AssignmentMissing)?,
        )?);
    }
    Ok(fe_bytes)
}

#[allow(clippy::too_many_arguments)]
pub fn execute_outer_circuit<C: Testnet2Components, CS: ConstraintSystem<C::OuterScalarField>>(
    cs: &mut CS,

    // Inner snark verifier public inputs
    ledger_digest: &MerkleTreeDigest<C::RecordCommitmentTreeParameters>,
    old_serial_numbers: &[<C::AccountSignatureScheme as SignatureScheme>::PublicKey],
    new_commitments: &[C::RecordCommitment],
    new_encrypted_record_hashes: &[C::EncryptedRecordDigest],
    memo: &<Transaction<C> as TransactionScheme>::Memorandum,
    value_balance: AleoAmount,
    network_id: u8,

    // Inner snark verifier private inputs (verifying key and proof)
    inner_snark_vk: &<C::InnerSNARK as SNARK>::VerifyingKey,
    inner_snark_proof: &<C::InnerSNARK as SNARK>::Proof,

    // Program verifying keys and proofs
    program_proofs: &[Execution<C::ProgramSNARK>],

    // Rest
    program_commitment: &<C::ProgramCommitmentScheme as CommitmentScheme>::Output,
    program_randomness: &<C::ProgramCommitmentScheme as CommitmentScheme>::Randomness,
    local_data_root: &C::LocalDataDigest,

    inner_circuit_id: &<C::InnerCircuitIDCRH as CRH>::Output,
) -> Result<(), SynthesisError> {
    // Declare public parameters.
    let (program_id_commitment_parameters, program_id_crh, inner_circuit_id_crh) = {
        let cs = &mut cs.ns(|| "Declare Comm and CRH parameters");

        let program_id_commitment_parameters = C::ProgramCommitmentGadget::alloc_constant(
            &mut cs.ns(|| "Declare program_id_commitment_parameters"),
            || Ok(C::program_commitment_scheme().clone()),
        )?;

        let program_id_crh: C::ProgramIDCRHGadget =
            C::ProgramIDCRHGadget::alloc_constant(&mut cs.ns(|| "Declare program_id_crh_parameters"), || {
                Ok(C::program_id_crh().clone())
            })?;

        let inner_circuit_id_crh = C::InnerCircuitIDCRHGadget::alloc_constant(
            &mut cs.ns(|| "Declare inner_circuit_id_crh_parameters"),
            || Ok(C::inner_circuit_id_crh().clone()),
        )?;

        (program_id_commitment_parameters, program_id_crh, inner_circuit_id_crh)
    };

    // ************************************************************************
    // Construct the InnerSNARK input
    // ************************************************************************

    // Declare inner snark verifier inputs as `CoreCheckF` field elements
    let ledger_digest_fe = ToConstraintField::<C::InnerScalarField>::to_field_elements(ledger_digest)
        .map_err(|_| SynthesisError::AssignmentMissing)?;

    let program_commitment_fe = program_commitment
        .to_field_elements()
        .map_err(|_| SynthesisError::AssignmentMissing)?;

    let memo_fe = ToConstraintField::<C::InnerScalarField>::to_field_elements(memo)
        .map_err(|_| SynthesisError::AssignmentMissing)?;

    let local_data_root_fe = ToConstraintField::<C::InnerScalarField>::to_field_elements(local_data_root)
        .map_err(|_| SynthesisError::AssignmentMissing)?;

    let value_balance_fe =
        ToConstraintField::<C::InnerScalarField>::to_field_elements(&value_balance.0.to_le_bytes()[..])
            .map_err(|_| SynthesisError::AssignmentMissing)?;

    let network_id_fe = ToConstraintField::<C::InnerScalarField>::to_field_elements(&[network_id][..])
        .map_err(|_| SynthesisError::AssignmentMissing)?;

    // Allocate field element bytes
    let ledger_digest_fe_bytes = alloc_input_field_element_to_bytes::<C, _>(cs, ledger_digest_fe, "ledger digest")?;

    let mut serial_number_fe_bytes = vec![];
    for (index, sn) in old_serial_numbers.iter().enumerate() {
        let serial_number_fe = ToConstraintField::<C::InnerScalarField>::to_field_elements(sn)
            .map_err(|_| SynthesisError::AssignmentMissing)?;

        serial_number_fe_bytes.extend(alloc_input_field_element_to_bytes::<C, _>(
            cs,
            serial_number_fe,
            &format!("Allocate serial number {:?}", index),
        )?);
    }

    let mut commitment_and_encrypted_record_hash_fe_bytes = vec![];
    for (index, (cm, encrypted_record_hash)) in new_commitments
        .iter()
        .zip_eq(new_encrypted_record_hashes.iter())
        .enumerate()
    {
        let commitment_fe = ToConstraintField::<C::InnerScalarField>::to_field_elements(cm)
            .map_err(|_| SynthesisError::AssignmentMissing)?;
        let encrypted_record_hash_fe =
            ToConstraintField::<C::InnerScalarField>::to_field_elements(encrypted_record_hash)
                .map_err(|_| SynthesisError::AssignmentMissing)?;

        commitment_and_encrypted_record_hash_fe_bytes.extend(alloc_input_field_element_to_bytes::<C, _>(
            cs,
            commitment_fe,
            &format!("Allocate record commitment {:?}", index),
        )?);

        commitment_and_encrypted_record_hash_fe_bytes.extend(alloc_input_field_element_to_bytes::<C, _>(
            cs,
            encrypted_record_hash_fe,
            &format!("Allocate encrypted record hash {:?}", index),
        )?);
    }

    let program_commitment_fe_bytes =
        alloc_field_element_to_bytes::<C, _>(cs, program_commitment_fe, "program commitment")?;
    let memo_fe_bytes = alloc_input_field_element_to_bytes::<C, _>(cs, memo_fe, "memo")?;
    let network_id_fe_bytes = alloc_input_field_element_to_bytes::<C, _>(cs, network_id_fe, "network id")?;
    let local_data_root_fe_bytes =
        alloc_field_element_to_bytes::<C, _>(cs, local_data_root_fe.clone(), "local data root")?;
    let value_balance_fe_bytes = alloc_input_field_element_to_bytes::<C, _>(cs, value_balance_fe, "value balance")?;

    // Construct inner snark input as bytes

    let mut inner_snark_input_bytes = vec![];
    inner_snark_input_bytes.extend(ledger_digest_fe_bytes);
    inner_snark_input_bytes.extend(serial_number_fe_bytes);
    inner_snark_input_bytes.extend(commitment_and_encrypted_record_hash_fe_bytes);
    inner_snark_input_bytes.extend(program_commitment_fe_bytes);
    inner_snark_input_bytes.extend(memo_fe_bytes);
    inner_snark_input_bytes.extend(network_id_fe_bytes);
    inner_snark_input_bytes.extend(local_data_root_fe_bytes.clone());
    inner_snark_input_bytes.extend(value_balance_fe_bytes);

    // Convert inner snark input bytes to bits

    let mut inner_snark_input_bits = Vec::with_capacity(inner_snark_input_bytes.len());
    for input_bytes in inner_snark_input_bytes {
        let input_bits = input_bytes
            .iter()
            .flat_map(|byte| byte.to_bits_le())
            .collect::<Vec<_>>();
        inner_snark_input_bits.push(input_bits);
    }

    // ************************************************************************
    // Verify the InnerSNARK proof
    // ************************************************************************

    let inner_snark_vk = <C::InnerSNARKGadget as SNARKVerifierGadget<_>>::VerificationKeyGadget::alloc(
        &mut cs.ns(|| "Allocate inner snark verifying key"),
        || Ok(inner_snark_vk),
    )?;

    let inner_snark_proof = <C::InnerSNARKGadget as SNARKVerifierGadget<_>>::ProofGadget::alloc(
        &mut cs.ns(|| "Allocate inner snark proof"),
        || Ok(inner_snark_proof),
    )?;

    C::InnerSNARKGadget::check_verify(
        &mut cs.ns(|| "Check that proof is satisfied"),
        &inner_snark_vk,
        inner_snark_input_bits.iter().filter(|inp| !inp.is_empty()).cloned(),
        &inner_snark_proof,
    )?;

    drop(inner_snark_input_bits);

    // ************************************************************************
    // Construct program input
    // ************************************************************************

    // Reuse inner snark verifier inputs

    let mut program_input_bytes = vec![];
    program_input_bytes.extend(local_data_root_fe_bytes);

    let mut program_input_bits = Vec::with_capacity(program_input_bytes.len());

    for input_bytes in program_input_bytes {
        let input_bits = input_bytes
            .iter()
            .flat_map(|byte| byte.to_bits_le())
            .collect::<Vec<_>>();
        if !input_bits.is_empty() {
            program_input_bits.push(input_bits);
        }
    }

    // ************************************************************************
    // ************************************************************************

    let mut old_death_program_ids = Vec::with_capacity(C::NUM_INPUT_RECORDS);
    let mut new_birth_program_ids = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);
    for (i, input) in program_proofs.iter().enumerate().take(C::NUM_INPUT_RECORDS) {
        let cs = &mut cs.ns(|| format!("Check death program for input record {}", i));

        let death_program_proof = <C::ProgramSNARKGadget as SNARKVerifierGadget<_>>::ProofGadget::alloc(
            &mut cs.ns(|| "Allocate proof"),
            || Ok(&input.proof),
        )?;

        let death_program_vk = <C::ProgramSNARKGadget as SNARKVerifierGadget<_>>::VerificationKeyGadget::alloc(
            &mut cs.ns(|| "Allocate verifying key"),
            || Ok(&input.verifying_key),
        )?;

        let death_program_vk_field_elements =
            death_program_vk.to_constraint_field(cs.ns(|| "alloc_death_program_vk_field_elements"))?;

        let claimed_death_program_id = program_id_crh.check_evaluation_gadget_on_field_elements(
            &mut cs.ns(|| "Compute death program ID"),
            death_program_vk_field_elements,
        )?;

        let claimed_death_program_id_bytes =
            claimed_death_program_id.to_bytes(&mut cs.ns(|| "Convert death program ID to bytes"))?;

        old_death_program_ids.push(claimed_death_program_id_bytes);

        let position_fe = vec![C::InnerScalarField::from(i as u128)];
        let mut program_input_field_elements = vec![];

        program_input_field_elements.extend(position_fe);
        program_input_field_elements.extend(local_data_root_fe.clone());

        let mut program_snark_input = vec![];

        for (j, input) in program_input_field_elements.iter().enumerate() {
            let input_element = <C::ProgramSNARKGadget as SNARKVerifierGadget<_>>::Input::alloc(
                cs.ns(|| format!("alloc_death_program_input_{}_{}", i, j)),
                || Ok(input),
            )?;

            program_snark_input.push(input_element);
        }

        C::ProgramSNARKGadget::check_verify(
            &mut cs.ns(|| "Check that proof is satisfied"),
            &death_program_vk,
            program_snark_input.iter().cloned(),
            &death_program_proof,
        )?;
    }

    for (j, input) in program_proofs
        .iter()
        .skip(C::NUM_INPUT_RECORDS)
        .enumerate()
        .take(C::NUM_OUTPUT_RECORDS)
    {
        let cs = &mut cs.ns(|| format!("Check birth program for output record {}", j));

        let birth_program_proof = <C::ProgramSNARKGadget as SNARKVerifierGadget<_>>::ProofGadget::alloc(
            &mut cs.ns(|| "Allocate proof"),
            || Ok(&input.proof),
        )?;

        let birth_program_vk = <C::ProgramSNARKGadget as SNARKVerifierGadget<_>>::VerificationKeyGadget::alloc(
            &mut cs.ns(|| "Allocate verifying key"),
            || Ok(&input.verifying_key),
        )?;

        let birth_program_vk_field_elements =
            birth_program_vk.to_constraint_field(cs.ns(|| "birth_death_program_vk_field_elements"))?;

        let claimed_birth_program_id = program_id_crh.check_evaluation_gadget_on_field_elements(
            &mut cs.ns(|| "Compute birth program ID"),
            birth_program_vk_field_elements,
        )?;

        let claimed_birth_program_id_bytes =
            claimed_birth_program_id.to_bytes(&mut cs.ns(|| "Convert birth program ID to bytes"))?;

        new_birth_program_ids.push(claimed_birth_program_id_bytes);

        let position_fe = vec![C::InnerScalarField::from((C::NUM_INPUT_RECORDS + j) as u128)];
        let mut program_input_field_elements = vec![];

        program_input_field_elements.extend(position_fe);
        program_input_field_elements.extend(local_data_root_fe.clone());

        let mut program_snark_input = vec![];

        for (k, input) in program_input_field_elements.iter().enumerate() {
            let input_element = <C::ProgramSNARKGadget as SNARKVerifierGadget<_>>::Input::alloc(
                cs.ns(|| format!("alloc_birth_program_input_{}_{}", j, k)),
                || Ok(input),
            )?;

            program_snark_input.push(input_element);
        }

        C::ProgramSNARKGadget::check_verify(
            &mut cs.ns(|| "Check that proof is satisfied"),
            &birth_program_vk,
            program_snark_input.iter().cloned(),
            &birth_program_proof,
        )?;
    }
    // ********************************************************************

    // ********************************************************************
    // Check that the program commitment is derived correctly.
    // ********************************************************************
    {
        let commitment_cs = &mut cs.ns(|| "Check that program commitment is well-formed");

        let mut input = Vec::new();
        for id in old_death_program_ids.iter().take(C::NUM_INPUT_RECORDS) {
            input.extend_from_slice(&id);
        }

        for id in new_birth_program_ids.iter().take(C::NUM_OUTPUT_RECORDS) {
            input.extend_from_slice(&id);
        }

        let given_commitment_randomness =
            <C::ProgramCommitmentGadget as CommitmentGadget<_, C::OuterScalarField>>::RandomnessGadget::alloc(
                &mut commitment_cs.ns(|| "Commitment randomness"),
                || Ok(program_randomness),
            )?;

        let given_commitment =
            <C::ProgramCommitmentGadget as CommitmentGadget<_, C::OuterScalarField>>::OutputGadget::alloc(
                &mut commitment_cs.ns(|| "Commitment output"),
                || Ok(program_commitment),
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
