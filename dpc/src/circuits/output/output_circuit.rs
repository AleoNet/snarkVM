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

use crate::{Network, OutputPrivateVariables, OutputPublicVariables, Payload};
use snarkvm_gadgets::{
    bits::{Boolean, ToBytesGadget},
    integers::uint::UInt8,
    traits::{
        algorithms::{CRHGadget, CommitmentGadget, EncryptionGadget},
        alloc::AllocGadget,
        eq::{ConditionalEqGadget, EqGadget},
    },
    FpGadget,
    ToConstraintFieldGadget,
};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSynthesizer, ConstraintSystem};
use snarkvm_utilities::{FromBytes, ToBytes};

#[derive(Clone)]
pub struct OutputCircuit<N: Network> {
    public: OutputPublicVariables<N>,
    private: OutputPrivateVariables<N>,
}

impl<N: Network> OutputCircuit<N> {
    pub fn blank() -> Self {
        Self { public: OutputPublicVariables::blank(), private: OutputPrivateVariables::blank() }
    }

    pub fn new(public: OutputPublicVariables<N>, private: OutputPrivateVariables<N>) -> Self {
        Self { public, private }
    }
}

impl<N: Network> ConstraintSynthesizer<N::InnerScalarField> for OutputCircuit<N> {
    fn generate_constraints<CS: ConstraintSystem<N::InnerScalarField>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let public = &self.public;
        let private = &self.private;

        let commitment = public.commitment();
        let value_commitment = public.output_value_commitment();

        let record = &private.output_record;
        let encryption_randomness = &private.encryption_randomness;
        let value_commitment_randomness = &private.output_value_commitment_randomness;

        // Declares a constant for a 0 value in a record.
        let zero_value = UInt8::constant_vec(&(0u64).to_bytes_le()?);
        // Declares a constant for an empty payload in a record.
        let empty_payload = UInt8::constant_vec(&Payload::<N>::default().to_bytes_le()?);
        // Declare the empty program ID as bytes.
        let empty_program_id_bytes = UInt8::constant_vec(&vec![0u8; N::PROGRAM_ID_SIZE_IN_BYTES]);

        // TODO: directly allocate these as the appropriate number of constant zero field elements
        // (i.e., no constraints)
        let zero_value_field_elements =
            zero_value.to_constraint_field(&mut cs.ns(|| "convert zero value to field elements"))?;
        let empty_payload_field_elements =
            empty_payload.to_constraint_field(&mut cs.ns(|| "convert empty payload to field elements"))?;
        let empty_program_id_field_elements =
            empty_program_id_bytes.to_constraint_field(&mut cs.ns(|| "convert empty program ID to field elements"))?;

        // Declare the program ID.
        let program_id_fe = {
            let program_id_bytes = public
                .program_id
                .map_or(Ok(vec![0u8; N::PROGRAM_ID_SIZE_IN_BYTES]), |program_id| program_id.to_bytes_le())?;
            let executable_program_id_bytes =
                UInt8::alloc_input_vec_le(&mut cs.ns(|| "Allocate executable_program_id"), &program_id_bytes)?;
            executable_program_id_bytes
                .to_constraint_field(&mut cs.ns(|| "convert executable program ID to field elements"))?
        };

        let (account_encryption_parameters, record_commitment_parameters, value_commitment_parameters) = {
            let cs = &mut cs.ns(|| "Declare parameters");

            let account_encryption_parameters = N::AccountEncryptionGadget::alloc_constant(
                &mut cs.ns(|| "Declare account encryption parameters"),
                || Ok(N::account_encryption_scheme().clone()),
            )?;

            let record_commitment_parameters =
                N::CommitmentGadget::alloc_constant(&mut cs.ns(|| "Declare record commitment parameters"), || {
                    Ok(N::commitment_scheme().clone())
                })?;

            let value_commitment_parameters = N::ValueCommitmentGadget::alloc_constant(
                &mut cs.ns(|| "Declare record value commitment parameters"),
                || Ok(N::value_commitment_scheme().clone()),
            )?;

            (account_encryption_parameters, record_commitment_parameters, value_commitment_parameters)
        };

        let cs = &mut cs.ns(|| "Process output record");

        let (given_owner, given_is_dummy, given_value_bytes, given_payload, given_program_id, given_randomizer) = {
            let declare_cs = &mut cs.ns(|| "Declare output record");

            let given_owner = <N::AccountEncryptionGadget as EncryptionGadget<
                N::AccountEncryptionScheme,
                N::InnerScalarField,
            >>::PublicKeyGadget::alloc(
                &mut declare_cs.ns(|| "given_record_owner"), || Ok(*record.owner())
            )?;

            let given_is_dummy = Boolean::alloc(&mut declare_cs.ns(|| "given_is_dummy"), || Ok(record.is_dummy()))?;

            let given_value_bytes =
                UInt8::alloc_vec(&mut declare_cs.ns(|| "given_value"), &record.value().to_bytes_le()?)?;

            // Use an empty payload if the record does not have one.
            let payload = record.payload().clone().unwrap_or_default();
            let given_payload = UInt8::alloc_vec(&mut declare_cs.ns(|| "given_payload"), &payload.to_bytes_le()?)?;

            // Use an empty program id if the record does not have one.
            let program_id_bytes = record
                .program_id()
                .map_or(Ok(vec![0u8; N::PROGRAM_ID_SIZE_IN_BYTES]), |program_id| program_id.to_bytes_le())?;
            let given_program_id = UInt8::alloc_vec(&mut declare_cs.ns(|| "given_program_id"), &program_id_bytes)?;

            let given_randomizer = <N::AccountEncryptionGadget as EncryptionGadget<
                N::AccountEncryptionScheme,
                N::InnerScalarField,
            >>::CiphertextRandomizer::alloc(
                &mut declare_cs.ns(|| "given_randomizer"), || Ok(record.randomizer())
            )?;

            (given_owner, given_is_dummy, given_value_bytes, given_payload, given_program_id, given_randomizer)
        };
        // ********************************************************************

        // *******************************************************************
        // Check that the record is well-formed.
        // *******************************************************************
        let value_bytes = {
            let commitment_cs = &mut cs.ns(|| "Check that record is well-formed");

            // *******************************************************************
            // Convert the owner, dummy flag, value, payload, program ID, and randomizer into bits.
            // *******************************************************************

            let given_is_dummy_bytes =
                given_is_dummy.to_bytes(&mut commitment_cs.ns(|| "Convert given_is_dummy to bytes"))?;

            {
                let given_value_field_elements = given_value_bytes
                    .to_constraint_field(&mut commitment_cs.ns(|| "convert given value to field elements"))?;
                let given_payload_field_elements = given_payload
                    .to_constraint_field(&mut commitment_cs.ns(|| "convert given payload to field elements"))?;
                let given_program_id_field_elements = given_program_id
                    .to_constraint_field(&mut commitment_cs.ns(|| "convert given program ID to field elements"))?;

                // Perform noop safety checks.
                given_value_field_elements.conditional_enforce_equal(
                    &mut commitment_cs.ns(|| "If the output record is empty, enforce it has a value of 0"),
                    &zero_value_field_elements,
                    &given_is_dummy,
                )?;
                given_payload_field_elements.conditional_enforce_equal(
                    &mut commitment_cs.ns(|| "If the output record is empty, enforce it has an empty payload"),
                    &empty_payload_field_elements,
                    &given_is_dummy,
                )?;
                given_program_id_field_elements.conditional_enforce_equal(
                    &mut commitment_cs.ns(|| "If the output record is empty, enforce it has an empty program ID"),
                    &empty_program_id_field_elements,
                    &given_is_dummy,
                )?;

                // Ensure the program ID matches the declared program ID (conditionally).
                given_program_id_field_elements.conditional_enforce_equal(
                    &mut commitment_cs.ns(|| "Check the-th output program ID matches"),
                    &program_id_fe,
                    &given_is_dummy.not(),
                )?;
            }

            // *******************************************************************
            // Check that the record ciphertext and commitment are well-formed.
            // *******************************************************************

            // TODO (howardwu): CRITICAL - Use given_owner by exposing the FpGadget in the signature trait.
            let owner_fe = FromBytes::read_le(&record.owner().to_bytes_le()?[..])?;
            let given_owner_gadget = FpGadget::alloc(&mut commitment_cs.ns(|| "Field element"), || Ok(&owner_fe))?;

            let encoded_given_value = <N::AccountEncryptionGadget as EncryptionGadget<
                N::AccountEncryptionScheme,
                N::InnerScalarField,
            >>::encode_message(
                &mut commitment_cs.ns(|| "encode input value"), &given_value_bytes
            )?;

            let encoded_given_payload = <N::AccountEncryptionGadget as EncryptionGadget<
                N::AccountEncryptionScheme,
                N::InnerScalarField,
            >>::encode_message(
                &mut commitment_cs.ns(|| "encode input payload"), &given_payload
            )?;

            let mut plaintext = Vec::with_capacity(1 + encoded_given_value.len() + encoded_given_payload.len());
            plaintext.push(given_owner_gadget);
            plaintext.extend_from_slice(&encoded_given_value);
            plaintext.extend_from_slice(&encoded_given_payload);

            let encryption_randomness = <N::AccountEncryptionGadget as EncryptionGadget<
                N::AccountEncryptionScheme,
                N::InnerScalarField,
            >>::ScalarRandomnessGadget::alloc(
                &mut commitment_cs.ns(|| "output record encryption_randomness"),
                || Ok(encryption_randomness),
            )?;

            let (candidate_ciphertext_randomizer, ciphertext, record_view_key) = account_encryption_parameters
                .check_encryption_from_scalar_randomness(
                    &mut commitment_cs.ns(|| "output record check_encryption_gadget"),
                    &encryption_randomness,
                    &given_owner,
                    &plaintext,
                )?;

            // Ensure the given randomizer is correct.
            candidate_ciphertext_randomizer.enforce_equal(
                &mut commitment_cs.ns(|| "Check that the given randomizer matches public input"),
                &given_randomizer,
            )?;

            // *******************************************************************
            // Compute the record commitment and check that it matches the declared commitment.
            // *******************************************************************

            let record_view_key_commitment = account_encryption_parameters.check_symmetric_key_commitment(
                &mut commitment_cs.ns(|| "output record check_symmetric_key_commitment"),
                &record_view_key,
            )?;

            let given_randomizer_bytes =
                given_randomizer.to_bytes(&mut commitment_cs.ns(|| "Convert given_randomizer to bytes"))?;
            let record_view_key_commitment_bytes = record_view_key_commitment
                .to_bytes(&mut commitment_cs.ns(|| "Convert record_view_key_commitment to bytes"))?;

            let ciphertext_bytes = ciphertext
                .iter()
                .enumerate()
                .flat_map(|(i, element)| {
                    element
                        .to_bytes(&mut commitment_cs.ns(|| format!("Convert output ciphertext {} to bytes", i)))
                        .unwrap()
                })
                .collect::<Vec<_>>();

            let mut commitment_input = Vec::with_capacity(
                given_randomizer_bytes.len()
                    + record_view_key_commitment_bytes.len()
                    + ciphertext_bytes.len()
                    + given_program_id.len()
                    + given_is_dummy_bytes.len(),
            );
            commitment_input.extend_from_slice(&given_randomizer_bytes);
            commitment_input.extend_from_slice(&record_view_key_commitment_bytes);
            commitment_input.extend_from_slice(&ciphertext_bytes);
            commitment_input.extend_from_slice(&given_program_id);
            commitment_input.extend_from_slice(&given_is_dummy_bytes);

            let candidate_commitment = record_commitment_parameters
                .check_evaluation_gadget(&mut commitment_cs.ns(|| "Compute record commitment"), commitment_input)?;

            let given_commitment = <N::CommitmentGadget as CRHGadget<
                N::CommitmentScheme,
                N::InnerScalarField,
            >>::OutputGadget::alloc_input(
                &mut commitment_cs.ns(|| "Allocate given output commitment"),
                || Ok(*commitment),
            )?;

            candidate_commitment.enforce_equal(
                &mut commitment_cs.ns(|| "Check that the-th output commitment is valid"),
                &given_commitment,
            )?;

            // output_values.push(given_value);

            given_value_bytes
        };

        // ********************************************************************
        // Check that the output value commitment is derived correctly.
        // ********************************************************************
        {
            let vc_cs = &mut cs.ns(|| "Check that value commitment is derived correctly");

            let value_commitment_randomness_gadget = <N::ValueCommitmentGadget as CommitmentGadget<
                N::ValueCommitmentScheme,
                N::InnerScalarField,
            >>::RandomnessGadget::alloc(
                &mut vc_cs.ns(|| "Output value commitment randomness"),
                || Ok(value_commitment_randomness),
            )?;

            let given_value_commitment_gadget = <N::ValueCommitmentGadget as CommitmentGadget<
                N::ValueCommitmentScheme,
                N::InnerScalarField,
            >>::OutputGadget::alloc_input(
                &mut vc_cs.ns(|| "Output value commitment"),
                || Ok(**value_commitment),
            )?;

            let candidate_value_commitment_gadget = value_commitment_parameters.check_commitment_gadget(
                &mut vc_cs.ns(|| "Compute output value commitment"),
                &value_bytes,
                &value_commitment_randomness_gadget,
            )?;

            candidate_value_commitment_gadget.enforce_equal(
                &mut vc_cs.ns(|| "Check that the-th output value commitment is valid"),
                &given_value_commitment_gadget,
            )?;
        }

        Ok(())
    }
}
