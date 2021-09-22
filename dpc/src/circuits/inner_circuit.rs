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

use crate::{ComputeKey, InnerPrivateVariables, InnerPublicVariables, Network, Payload, RecordScheme};
use snarkvm_algorithms::traits::*;
use snarkvm_gadgets::{
    algorithms::merkle_tree::merkle_path::MerklePathGadget,
    bits::{Boolean, ToBytesGadget},
    integers::{int::Int64, uint::UInt8},
    traits::{
        algorithms::{CRHGadget, CommitmentGadget, EncryptionGadget, PRFGadget, SignatureGadget},
        alloc::AllocGadget,
        eq::{ConditionalEqGadget, EqGadget},
        integers::{add::Add, integer::Integer, sub::Sub},
    },
    ToConstraintFieldGadget,
};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSynthesizer, ConstraintSystem};
use snarkvm_utilities::{FromBytes, ToBytes};

use itertools::Itertools;

#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"))]
pub struct InnerCircuit<N: Network> {
    public: InnerPublicVariables<N>,
    private: InnerPrivateVariables<N>,
}

impl<N: Network> InnerCircuit<N> {
    pub fn blank() -> Self {
        Self {
            public: InnerPublicVariables::blank(),
            private: InnerPrivateVariables::blank(),
        }
    }

    pub fn new(public: InnerPublicVariables<N>, private: InnerPrivateVariables<N>) -> Self {
        Self { public, private }
    }
}

impl<N: Network> ConstraintSynthesizer<N::InnerScalarField> for InnerCircuit<N> {
    fn generate_constraints<CS: ConstraintSystem<N::InnerScalarField>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let public = &self.public;
        let private = &self.private;

        // In the inner circuit, these two variables must be allocated as public inputs.
        debug_assert!(public.program_commitment.is_some());
        debug_assert!(public.local_data_root.is_some());

        let (
            account_encryption_parameters,
            account_signature_parameters,
            record_commitment_parameters,
            encrypted_record_crh,
            program_commitment_parameters,
            local_data_crh,
            local_data_commitment_parameters,
            commitments_tree_parameters,
        ) = {
            let cs = &mut cs.ns(|| "Declare parameters");

            let account_encryption_parameters = N::AccountEncryptionGadget::alloc_constant(
                &mut cs.ns(|| "Declare account encryption parameters"),
                || Ok(N::account_encryption_scheme().clone()),
            )?;

            let account_signature_parameters = N::AccountSignatureGadget::alloc_constant(
                &mut cs.ns(|| "Declare account signature parameters"),
                || Ok(N::account_signature_scheme().clone()),
            )?;

            let record_commitment_parameters =
                N::CommitmentGadget::alloc_constant(&mut cs.ns(|| "Declare record commitment parameters"), || {
                    Ok(N::commitment_scheme().clone())
                })?;

            let encrypted_record_crh_parameters = N::EncryptedRecordCRHGadget::alloc_constant(
                &mut cs.ns(|| "Declare record ciphertext CRH parameters"),
                || Ok(N::encrypted_record_crh().clone()),
            )?;

            let program_commitment_parameters = N::ProgramCommitmentGadget::alloc_constant(
                &mut cs.ns(|| "Declare program commitment parameters"),
                || Ok(N::program_commitment_scheme().clone()),
            )?;

            let local_data_crh_parameters =
                N::LocalDataCRHGadget::alloc_constant(&mut cs.ns(|| "Declare local data CRH parameters"), || {
                    Ok(N::local_data_crh().clone())
                })?;

            let local_data_commitment_parameters = N::LocalDataCommitmentGadget::alloc_constant(
                &mut cs.ns(|| "Declare local data commitment parameters"),
                || Ok(N::local_data_commitment_scheme().clone()),
            )?;

            let commitments_tree_parameters = N::CommitmentsTreeCRHGadget::alloc_constant(
                &mut cs.ns(|| "Declare commitments tree CRH parameters"),
                || Ok(N::commitments_tree_parameters().crh()),
            )?;

            (
                account_encryption_parameters,
                account_signature_parameters,
                record_commitment_parameters,
                encrypted_record_crh_parameters,
                program_commitment_parameters,
                local_data_crh_parameters,
                local_data_commitment_parameters,
                commitments_tree_parameters,
            )
        };

        // Declares a constant for a 0 value in a record.
        let zero_value = UInt8::constant_vec(&(0u64).to_bytes_le()?);
        // Declares a constant for an empty payload in a record.
        let empty_payload = UInt8::constant_vec(&Payload::default().to_bytes_le()?);

        let zero_value_field_elements =
            zero_value.to_constraint_field(&mut cs.ns(|| "convert zero value to field elements"))?;
        let empty_payload_field_elements =
            empty_payload.to_constraint_field(&mut cs.ns(|| "convert empty payload to field elements"))?;

        let digest_gadget = <N::CommitmentsTreeCRHGadget as CRHGadget<_, _>>::OutputGadget::alloc_input(
            &mut cs.ns(|| "Declare ledger digest"),
            || Ok(public.ledger_digest),
        )?;

        let mut old_serial_numbers_gadgets = Vec::with_capacity(private.input_records.len());
        let mut old_serial_numbers_bytes_gadgets = Vec::with_capacity(private.input_records.len() * 32); // Serial numbers are 32 bytes
        let mut old_record_commitments_gadgets = Vec::with_capacity(private.input_records.len());
        let mut old_program_ids_gadgets = Vec::with_capacity(private.input_records.len());
        let mut signature_public_keys = Vec::with_capacity(private.input_records.len());

        for (i, (((record, witness), signature), given_serial_number)) in private
            .input_records
            .iter()
            .zip(&private.input_witnesses)
            .zip(&private.signatures)
            .zip(public.kernel.serial_numbers())
            .enumerate()
        {
            let cs = &mut cs.ns(|| format!("Process input record {}", i));

            // Declare record contents
            let (
                given_program_id,
                given_owner,
                given_is_dummy,
                given_value,
                given_payload,
                given_serial_number_nonce,
                given_commitment,
                given_commitment_randomness,
            ) = {
                let declare_cs = &mut cs.ns(|| "Declare input record");

                let given_program_id = UInt8::alloc_vec(
                    &mut declare_cs.ns(|| "given_program_id"),
                    &record.program_id().to_bytes_le()?,
                )?;
                old_program_ids_gadgets.push(given_program_id.clone());

                // No need to check that commitments, public keys and hashes are in
                // prime order subgroup because the commitment and CRH parameters
                // are trusted, and so when we recompute these, the newly computed
                // values will always be in correct subgroup. If the input cm, pk
                // or hash is incorrect, then it will not match the computed equivalent.
                let given_owner = <N::AccountEncryptionGadget as EncryptionGadget<
                    N::AccountEncryptionScheme,
                    N::InnerScalarField,
                >>::PublicKeyGadget::alloc(
                    &mut declare_cs.ns(|| "given_record_owner"),
                    || Ok(record.owner().encryption_key()),
                )?;

                // TODO (howardwu): TEMPORARY - Unify this with `given_owner` above!
                // Save the given_owner for signature verification at the end.
                {
                    let owner = record.owner().encryption_key();
                    let public_key = FromBytes::read_le(&owner.to_bytes_le()?[..])?;
                    let public_key_gadget = <N::AccountSignatureGadget as SignatureGadget<
                        N::AccountSignatureScheme,
                        N::InnerScalarField,
                    >>::PublicKeyGadget::alloc(
                        declare_cs.ns(|| format!("alloc_public_key{}", i)), || Ok(&public_key)
                    )?;
                    signature_public_keys.push(public_key_gadget);
                }

                let given_is_dummy = Boolean::alloc(&mut declare_cs.ns(|| "given_is_dummy"), || Ok(record.is_dummy()))?;

                let given_value =
                    UInt8::alloc_vec(&mut declare_cs.ns(|| "given_value"), &record.value().to_bytes_le()?)?;

                let given_payload =
                    UInt8::alloc_vec(&mut declare_cs.ns(|| "given_payload"), &record.payload().to_bytes_le()?)?;

                let given_serial_number_nonce =
                    <N::SerialNumberPRFGadget as PRFGadget<N::SerialNumberPRF, N::InnerScalarField>>::Input::alloc(
                        &mut declare_cs.ns(|| "given_serial_number_nonce"),
                        || Ok(vec![record.serial_number_nonce().clone()]),
                    )?;

                let given_commitment = <N::CommitmentGadget as CommitmentGadget<
                    N::CommitmentScheme,
                    N::InnerScalarField,
                >>::OutputGadget::alloc(
                    &mut declare_cs.ns(|| "given_commitment"), || Ok(record.commitment())
                )?;
                old_record_commitments_gadgets.push(given_commitment.clone());

                let given_commitment_randomness = <N::CommitmentGadget as CommitmentGadget<
                    N::CommitmentScheme,
                    N::InnerScalarField,
                >>::RandomnessGadget::alloc(
                    &mut declare_cs.ns(|| "given_commitment_randomness"),
                    || Ok(record.commitment_randomness()),
                )?;

                (
                    given_program_id,
                    given_owner,
                    given_is_dummy,
                    given_value,
                    given_payload,
                    given_serial_number_nonce,
                    given_commitment,
                    given_commitment_randomness,
                )
            };

            // **********************************************************************************
            // Check that the commitment appears on the ledger,
            // i.e., the membership witness is valid with respect to the record commitment root.
            // **********************************************************************************
            {
                let witness_cs = &mut cs.ns(|| "Check ledger membership witness");

                let witness_gadget = MerklePathGadget::<_, N::CommitmentsTreeCRHGadget, _>::alloc(
                    &mut witness_cs.ns(|| "Declare membership witness"),
                    || Ok(witness),
                )?;

                witness_gadget.conditionally_check_membership(
                    &mut witness_cs.ns(|| "Perform ledger membership witness check"),
                    &commitments_tree_parameters,
                    &digest_gadget,
                    &given_commitment,
                    &given_is_dummy.not(),
                )?;
            }
            // ********************************************************************

            // ********************************************************************
            // Check that the serial number is derived correctly.
            // ********************************************************************
            {
                let sn_cs = &mut cs.ns(|| "Check that sn is derived correctly");

                // TODO (howardwu): CRITICAL - Review the translation from scalar to base field of `sk_prf`.
                // Allocate sk_prf.
                let sk_prf = {
                    let compute_key = ComputeKey::<N>::from_signature(&signature)
                        .expect("Failed to derive the compute key from signature");
                    FromBytes::read_le(&compute_key.sk_prf().to_bytes_le()?[..])?
                };

                let sk_prf =
                    <N::SerialNumberPRFGadget as PRFGadget<N::SerialNumberPRF, N::InnerScalarField>>::Seed::alloc(
                        &mut sn_cs.ns(|| "Declare sk_prf"),
                        || Ok(&sk_prf),
                    )?;

                let candidate_serial_number_gadget = <N::SerialNumberPRFGadget as PRFGadget<
                    N::SerialNumberPRF,
                    N::InnerScalarField,
                >>::check_evaluation_gadget(
                    &mut sn_cs.ns(|| "Compute serial number"),
                    &sk_prf,
                    &given_serial_number_nonce,
                )?;

                let given_serial_number_gadget = <N::SerialNumberPRFGadget as PRFGadget<
                    N::SerialNumberPRF,
                    N::InnerScalarField,
                >>::Output::alloc_input(
                    &mut sn_cs.ns(|| "Declare given serial number"),
                    || Ok(given_serial_number),
                )?;

                candidate_serial_number_gadget.enforce_equal(
                    &mut sn_cs.ns(|| "Check that given and computed serial numbers are equal"),
                    &given_serial_number_gadget,
                )?;

                // Convert input serial numbers to bytes.
                old_serial_numbers_bytes_gadgets.extend_from_slice(
                    &candidate_serial_number_gadget
                        .to_bytes(&mut sn_cs.ns(|| format!("Convert {}-th serial number to bytes", i)))?,
                );

                old_serial_numbers_gadgets.push(candidate_serial_number_gadget);
            };
            // ********************************************************************

            // *******************************************************************
            // Check that the record is well-formed.
            // *******************************************************************
            {
                let commitment_cs = &mut cs.ns(|| "Check that record is well-formed");

                // Perform noop safety checks.
                {
                    let given_value_field_elements = given_value
                        .to_constraint_field(&mut commitment_cs.ns(|| "convert given value to field elements"))?;
                    let given_payload_field_elements = given_payload
                        .to_constraint_field(&mut commitment_cs.ns(|| "convert given payload to field elements"))?;

                    given_value_field_elements.conditional_enforce_equal(
                        &mut commitment_cs
                            .ns(|| format!("If the input record {} is a noop, enforce it has a value of 0", i)),
                        &zero_value_field_elements,
                        &given_is_dummy,
                    )?;
                    given_payload_field_elements.conditional_enforce_equal(
                        &mut commitment_cs
                            .ns(|| format!("If the input record {} is a noop, enforce it has an empty payload", i)),
                        &empty_payload_field_elements,
                        &given_is_dummy,
                    )?;
                }

                // Compute the record commitment and check that it matches the declared commitment.
                let record_owner_bytes =
                    given_owner.to_bytes(&mut commitment_cs.ns(|| "Convert record_owner to bytes"))?;
                let is_dummy_bytes = given_is_dummy.to_bytes(&mut commitment_cs.ns(|| "Convert is_dummy to bytes"))?;
                let serial_number_nonce_bytes = given_serial_number_nonce
                    .to_bytes(&mut commitment_cs.ns(|| "Convert given_serial_number_nonce to bytes"))?;

                let mut commitment_input = Vec::new();
                commitment_input.extend_from_slice(&given_program_id);
                commitment_input.extend_from_slice(&record_owner_bytes);
                commitment_input.extend_from_slice(&is_dummy_bytes);
                commitment_input.extend_from_slice(&given_value);
                commitment_input.extend_from_slice(&given_payload);
                commitment_input.extend_from_slice(&serial_number_nonce_bytes);

                let candidate_commitment = record_commitment_parameters.check_commitment_gadget(
                    &mut commitment_cs.ns(|| "Compute commitment"),
                    &commitment_input,
                    &given_commitment_randomness,
                )?;

                candidate_commitment.enforce_equal(
                    &mut commitment_cs.ns(|| "Check that declared and computed commitments are equal"),
                    &given_commitment,
                )?;
            }
        }

        let mut output_commitments = Vec::with_capacity(private.output_records.len());
        let mut output_commitments_bytes = Vec::with_capacity(private.output_records.len() * 32); // Commitments are 32 bytes
        let mut new_program_ids_gadgets = Vec::with_capacity(private.output_records.len());

        for (j, (((record, commitment), encryption_randomness), encrypted_record_hash)) in private
            .output_records
            .iter()
            .zip(public.kernel.commitments())
            .zip(&private.encrypted_record_randomizers)
            .zip(&public.encrypted_record_hashes)
            .enumerate()
        {
            let cs = &mut cs.ns(|| format!("Process output record {}", j));

            let (
                given_program_id,
                given_owner,
                given_is_dummy,
                given_value,
                given_payload,
                given_serial_number_nonce,
                given_serial_number_nonce_bytes,
                given_commitment,
                given_commitment_randomness,
            ) = {
                let declare_cs = &mut cs.ns(|| "Declare output record");

                let given_program_id = UInt8::alloc_vec(
                    &mut declare_cs.ns(|| "given_program_id"),
                    &record.program_id().to_bytes_le()?,
                )?;
                new_program_ids_gadgets.push(given_program_id.clone());

                let given_owner = <N::AccountEncryptionGadget as EncryptionGadget<
                    N::AccountEncryptionScheme,
                    N::InnerScalarField,
                >>::PublicKeyGadget::alloc(
                    &mut declare_cs.ns(|| "given_record_owner"),
                    || Ok(record.owner().encryption_key()),
                )?;

                let given_is_dummy = Boolean::alloc(&mut declare_cs.ns(|| "given_is_dummy"), || Ok(record.is_dummy()))?;

                let given_value =
                    UInt8::alloc_vec(&mut declare_cs.ns(|| "given_value"), &record.value().to_bytes_le()?)?;

                let given_payload =
                    UInt8::alloc_vec(&mut declare_cs.ns(|| "given_payload"), &record.payload().to_bytes_le()?)?;

                let given_serial_number_nonce =
                    <N::SerialNumberPRFGadget as PRFGadget<N::SerialNumberPRF, N::InnerScalarField>>::Output::alloc(
                        &mut declare_cs.ns(|| "given_serial_number_nonce"),
                        || Ok(record.serial_number_nonce()),
                    )?;

                let given_serial_number_nonce_bytes =
                    given_serial_number_nonce.to_bytes(&mut declare_cs.ns(|| "Convert sn nonce to bytes"))?;

                let given_commitment = {
                    let record_commitment = <N::CommitmentGadget as CommitmentGadget<
                        N::CommitmentScheme,
                        N::InnerScalarField,
                    >>::OutputGadget::alloc(
                        &mut declare_cs.ns(|| "record_commitment"), || Ok(record.commitment())
                    )?;

                    let public_commitment = <N::CommitmentGadget as CommitmentGadget<
                        N::CommitmentScheme,
                        N::InnerScalarField,
                    >>::OutputGadget::alloc_input(
                        &mut declare_cs.ns(|| "public_commitment"), || Ok(commitment)
                    )?;

                    record_commitment.enforce_equal(
                        &mut declare_cs.ns(|| "Check that record commitment matches the public commitment"),
                        &public_commitment,
                    )?;

                    record_commitment
                };
                output_commitments.push(given_commitment.clone());
                output_commitments_bytes
                    .extend_from_slice(&given_commitment.to_bytes(&mut declare_cs.ns(|| "commitment_bytes"))?);

                let given_commitment_randomness = <N::CommitmentGadget as CommitmentGadget<
                    N::CommitmentScheme,
                    N::InnerScalarField,
                >>::RandomnessGadget::alloc(
                    &mut declare_cs.ns(|| "given_commitment_randomness"),
                    || Ok(record.commitment_randomness()),
                )?;

                (
                    given_program_id,
                    given_owner,
                    given_is_dummy,
                    given_value,
                    given_payload,
                    given_serial_number_nonce,
                    given_serial_number_nonce_bytes,
                    given_commitment,
                    given_commitment_randomness,
                )
            };
            // ********************************************************************

            // *******************************************************************
            // Check that the serial number nonce is correct.
            // *******************************************************************
            {
                let sn_cs = &mut cs.ns(|| "Check that serial number nonce is correct");

                let candidate_serial_number_nonce = &old_serial_numbers_gadgets[j];

                candidate_serial_number_nonce.enforce_equal(
                    &mut sn_cs.ns(|| "Check that computed nonce matches provided nonce"),
                    &given_serial_number_nonce,
                )?;
            }
            // *******************************************************************

            // *******************************************************************
            // Check that the record is well-formed.
            // *******************************************************************
            {
                let commitment_cs = &mut cs.ns(|| "Check that record is well-formed");

                // Perform noop safety checks.
                {
                    let given_value_field_elements = given_value
                        .to_constraint_field(&mut commitment_cs.ns(|| "convert given value to field elements"))?;
                    let given_payload_field_elements = given_payload
                        .to_constraint_field(&mut commitment_cs.ns(|| "convert given payload to field elements"))?;

                    given_value_field_elements.conditional_enforce_equal(
                        &mut commitment_cs
                            .ns(|| format!("If the output record {} is a noop, enforce it has a value of 0", j)),
                        &zero_value_field_elements,
                        &given_is_dummy,
                    )?;
                    given_payload_field_elements.conditional_enforce_equal(
                        &mut commitment_cs
                            .ns(|| format!("If the output record {} is a noop, enforce it has an empty payload", j)),
                        &empty_payload_field_elements,
                        &given_is_dummy,
                    )?;
                }

                // Compute the record commitment and check that it matches the declared commitment.
                let given_owner_bytes =
                    given_owner.to_bytes(&mut commitment_cs.ns(|| "Convert record_owner to bytes"))?;
                let given_is_dummy_bytes =
                    given_is_dummy.to_bytes(&mut commitment_cs.ns(|| "Convert is_dummy to bytes"))?;

                let mut commitment_input = Vec::new();
                commitment_input.extend_from_slice(&given_program_id);
                commitment_input.extend_from_slice(&given_owner_bytes);
                commitment_input.extend_from_slice(&given_is_dummy_bytes);
                commitment_input.extend_from_slice(&given_value);
                commitment_input.extend_from_slice(&given_payload);
                commitment_input.extend_from_slice(&given_serial_number_nonce_bytes);

                let candidate_commitment = record_commitment_parameters.check_commitment_gadget(
                    &mut commitment_cs.ns(|| "Compute record commitment"),
                    &commitment_input,
                    &given_commitment_randomness,
                )?;
                candidate_commitment.enforce_equal(
                    &mut commitment_cs.ns(|| "Check that computed commitment matches public input"),
                    &given_commitment,
                )?;
            }

            // *******************************************************************

            // *******************************************************************
            // Check that the record encryption is well-formed.
            // *******************************************************************
            {
                let encryption_cs = &mut cs.ns(|| "Check that record encryption is well-formed");

                // Check serialization

                // *******************************************************************
                // Convert program id, value, payload, serial number nonce, and commitment randomness into bits.

                let plaintext_bytes = {
                    let mut res = vec![];

                    // Program ID
                    res.extend_from_slice(&given_program_id);

                    // Value
                    res.extend_from_slice(&given_value);

                    // Payload
                    res.extend_from_slice(&given_payload);

                    // Serial number nonce
                    res.extend_from_slice(&given_serial_number_nonce_bytes);

                    // Commitment randomness
                    let given_commitment_randomness_bytes = given_commitment_randomness
                        .to_bytes(&mut encryption_cs.ns(|| "Convert commitment randomness to bytes"))?;
                    res.extend_from_slice(&given_commitment_randomness_bytes);

                    res
                };

                // *******************************************************************
                // Construct the record encryption

                let encryption_randomness_gadget = <N::AccountEncryptionGadget as EncryptionGadget<
                    N::AccountEncryptionScheme,
                    N::InnerScalarField,
                >>::RandomnessGadget::alloc(
                    &mut encryption_cs.ns(|| format!("output record {} encryption_randomness", j)),
                    || Ok(encryption_randomness),
                )?;

                let candidate_encrypted_record_gadget = account_encryption_parameters.check_encryption_gadget(
                    &mut encryption_cs.ns(|| format!("output record {} check_encryption_gadget", j)),
                    &encryption_randomness_gadget,
                    &given_owner,
                    &plaintext_bytes,
                )?;

                // *******************************************************************
                // Check that the encrypted record hash is correct

                let encrypted_record_hash_gadget = <N::EncryptedRecordCRHGadget as CRHGadget<
                    N::EncryptedRecordCRH,
                    N::InnerScalarField,
                >>::OutputGadget::alloc_input(
                    &mut encryption_cs.ns(|| format!("output record {} encrypted record hash", j)),
                    || Ok(encrypted_record_hash),
                )?;

                let candidate_encrypted_record_hash = encrypted_record_crh.check_evaluation_gadget(
                    &mut encryption_cs.ns(|| format!("Compute encrypted record hash {}", j)),
                    candidate_encrypted_record_gadget,
                )?;

                encrypted_record_hash_gadget.enforce_equal(
                    encryption_cs.ns(|| format!("output record {} encrypted record hash is valid", j)),
                    &candidate_encrypted_record_hash,
                )?;
            }
        }
        // *******************************************************************

        // *******************************************************************
        // Check that program commitment is well-formed.
        // *******************************************************************
        {
            let commitment_cs = &mut cs.ns(|| "Check that program commitment is well-formed");

            // Check that each input record and output record at corresponding indices
            // have matching program IDs (e.g. input 1 and output 1 have the same program ID).
            for (index, (input_program_id, output_program_id)) in old_program_ids_gadgets
                .iter()
                .zip_eq(new_program_ids_gadgets.iter())
                .take(N::NUM_INPUT_RECORDS)
                .enumerate()
            {
                input_program_id.enforce_equal(
                    &mut commitment_cs
                        .ns(|| format!("Check that input and output record {} have matching program IDs", index)),
                    &output_program_id,
                )?;
            }

            // *******************************************************************

            let mut input = Vec::new();
            for id_gadget in old_program_ids_gadgets.iter().take(N::NUM_INPUT_RECORDS) {
                input.extend_from_slice(id_gadget);
            }
            for id_gadget in new_program_ids_gadgets.iter().take(N::NUM_OUTPUT_RECORDS) {
                input.extend_from_slice(id_gadget);
            }

            let given_commitment_randomness =
                <N::ProgramCommitmentGadget as CommitmentGadget<_, N::InnerScalarField>>::RandomnessGadget::alloc(
                    &mut commitment_cs.ns(|| "given_commitment_randomness"),
                    || Ok(&private.program_randomness),
                )?;

            let given_commitment =
                <N::ProgramCommitmentGadget as CommitmentGadget<_, N::InnerScalarField>>::OutputGadget::alloc_input(
                    &mut commitment_cs.ns(|| "given_commitment"),
                    || Ok(public.program_commitment.as_ref().unwrap()),
                )?;

            let candidate_commitment = program_commitment_parameters.check_commitment_gadget(
                &mut commitment_cs.ns(|| "candidate_commitment"),
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
        // Check that the local data root is valid.
        // ********************************************************************
        let (network_id, memo) = {
            let mut cs = cs.ns(|| "Check that local data root is valid.");

            let memo = UInt8::alloc_input_vec_le(cs.ns(|| "Allocate memorandum"), &*public.kernel.memo())?;
            let network_id = UInt8::alloc_input_vec_le(
                cs.ns(|| "Allocate network id"),
                &public.kernel.network_id().to_le_bytes(),
            )?;

            let mut local_data_input_commitment_bytes = vec![];
            for i in 0..N::NUM_INPUT_RECORDS {
                let mut cs = cs.ns(|| format!("Construct local data with input record {}", i));

                let mut input_bytes = vec![];
                input_bytes.extend_from_slice(&[UInt8::constant(i as u8)]);
                input_bytes.extend_from_slice(&old_serial_numbers_gadgets[i].to_bytes(&mut cs.ns(|| "serial_number"))?);
                input_bytes
                    .extend_from_slice(&old_record_commitments_gadgets[i].to_bytes(&mut cs.ns(|| "commitment"))?);
                input_bytes.extend_from_slice(&memo);
                input_bytes.extend_from_slice(&network_id);

                let commitment_randomness = <N::LocalDataCommitmentGadget as CommitmentGadget<
                    N::LocalDataCommitmentScheme,
                    N::InnerScalarField,
                >>::RandomnessGadget::alloc(
                    cs.ns(|| format!("Allocate old record local data commitment randomness {}", i)),
                    || Ok(&private.local_data_leaf_randomizers[i]),
                )?;

                let commitment = local_data_commitment_parameters.check_commitment_gadget(
                    cs.ns(|| format!("Commit to old record local data {}", i)),
                    &input_bytes,
                    &commitment_randomness,
                )?;

                local_data_input_commitment_bytes
                    .extend_from_slice(&commitment.to_bytes(&mut cs.ns(|| "old_record_local_data"))?);
            }

            let mut local_data_output_commitment_bytes = Vec::new();
            for j in 0..N::NUM_OUTPUT_RECORDS {
                let mut cs = cs.ns(|| format!("Construct local data with output record {}", j));

                let mut input_bytes = vec![];
                input_bytes.extend_from_slice(&[UInt8::constant((N::NUM_INPUT_RECORDS + j) as u8)]);
                input_bytes.extend_from_slice(&output_commitments[j].to_bytes(&mut cs.ns(|| "commitment"))?);
                input_bytes.extend_from_slice(&memo);
                input_bytes.extend_from_slice(&network_id);

                let commitment_randomness = <N::LocalDataCommitmentGadget as CommitmentGadget<
                    N::LocalDataCommitmentScheme,
                    N::InnerScalarField,
                >>::RandomnessGadget::alloc(
                    cs.ns(|| format!("Allocate new record local data commitment randomness {}", j)),
                    || Ok(&private.local_data_leaf_randomizers[N::NUM_INPUT_RECORDS + j]),
                )?;

                let commitment = local_data_commitment_parameters.check_commitment_gadget(
                    cs.ns(|| format!("Commit to new record local data {}", j)),
                    &input_bytes,
                    &commitment_randomness,
                )?;

                local_data_output_commitment_bytes
                    .extend_from_slice(&commitment.to_bytes(&mut cs.ns(|| "new_record_local_data"))?);
            }

            let inner1_commitment_hash = local_data_crh.check_evaluation_gadget(
                cs.ns(|| "Compute to local data commitment inner1 hash"),
                local_data_input_commitment_bytes,
            )?;

            let inner2_commitment_hash = local_data_crh.check_evaluation_gadget(
                cs.ns(|| "Compute to local data commitment inner2 hash"),
                local_data_output_commitment_bytes,
            )?;

            let mut inner_commitment_hash_bytes = Vec::new();
            inner_commitment_hash_bytes
                .extend_from_slice(&inner1_commitment_hash.to_bytes(&mut cs.ns(|| "inner1_commitment_hash"))?);
            inner_commitment_hash_bytes
                .extend_from_slice(&inner2_commitment_hash.to_bytes(&mut cs.ns(|| "inner2_commitment_hash"))?);

            let candidate_local_data_root = local_data_crh.check_evaluation_gadget(
                cs.ns(|| "Compute to local data commitment root"),
                inner_commitment_hash_bytes,
            )?;

            let given_local_data_root =
                <N::LocalDataCRHGadget as CRHGadget<N::LocalDataCRH, N::InnerScalarField>>::OutputGadget::alloc_input(
                    cs.ns(|| "Allocate local data root"),
                    || Ok(public.local_data_root.unwrap()),
                )?;

            candidate_local_data_root.enforce_equal(
                &mut cs.ns(|| "Check that local data root is valid"),
                &given_local_data_root,
            )?;

            (network_id, memo)
        };
        // *******************************************************************

        // *******************************************************************
        // Check that the value balance is valid.
        // *******************************************************************
        let value_balance = {
            let mut cs = cs.ns(|| "Check that the value balance is valid.");

            let given_value_balance =
                Int64::alloc_input_fe(cs.ns(|| "given_value_balance"), public.kernel.value_balance().0)?;

            let mut candidate_value_balance = Int64::zero();

            for (i, old_record) in private.input_records.iter().enumerate() {
                let value = old_record.value as i64;
                let record_value = Int64::alloc(cs.ns(|| format!("old record {} value", i)), || Ok(value))?;

                candidate_value_balance = candidate_value_balance
                    .add(cs.ns(|| format!("add old record {} value", i)), &record_value)
                    .unwrap();
            }

            for (j, new_record) in private.output_records.iter().enumerate() {
                let value = new_record.value as i64;
                let record_value = Int64::alloc(cs.ns(|| format!("new record {} value", j)), || Ok(value))?;

                candidate_value_balance = candidate_value_balance
                    .sub(cs.ns(|| format!("sub new record {} value", j)), &record_value)
                    .unwrap();
            }

            // Enforce that given_value_balance is equivalent to candidate_value_balance
            given_value_balance.enforce_equal(
                cs.ns(|| "given_value_balance == candidate_value_balance"),
                &candidate_value_balance,
            )?;

            given_value_balance
        };

        // *******************************************************************
        // Check that the signatures are valid.
        // *******************************************************************
        {
            let signature_cs = &mut cs.ns(|| "Check that signature is valid");

            // Encode the transaction kernel as the signature message.
            let mut message = Vec::new();
            message.extend_from_slice(&network_id);
            message.extend_from_slice(&old_serial_numbers_bytes_gadgets);
            message.extend_from_slice(&output_commitments_bytes);
            message.extend_from_slice(&value_balance.to_bytes(&mut signature_cs.ns(|| "value_balance_bytes"))?);
            message.extend_from_slice(&memo);

            // Verify each signature is valid.
            for (i, (signature, public_key)) in private.signatures.iter().zip(signature_public_keys).enumerate() {
                let signature_gadget = <N::AccountSignatureGadget as SignatureGadget<
                    N::AccountSignatureScheme,
                    N::InnerScalarField,
                >>::SignatureGadget::alloc(
                    signature_cs.ns(|| format!("alloc_signature_{}", i)), || Ok(signature)
                )?;

                let verification = account_signature_parameters.verify(
                    signature_cs.ns(|| format!("verify_{}", i)),
                    &public_key,
                    &message,
                    &signature_gadget,
                )?;

                verification.enforce_equal(
                    signature_cs.ns(|| format!("check_verification_{}", i)),
                    &Boolean::constant(true),
                )?;
            }
        }

        Ok(())
    }
}
