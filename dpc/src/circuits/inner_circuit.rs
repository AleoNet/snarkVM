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

use crate::{InnerPrivateVariables, InnerPublicVariables, Network, Payload, Transition, ValueBalanceCommitmentGadget};
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
    FpGadget,
    ToBitsLEGadget,
    ToConstraintFieldGadget,
};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSynthesizer, ConstraintSystem};
use snarkvm_utilities::{FromBytes, ToBytes};

use itertools::Itertools;

#[derive(Clone)]
pub struct InnerCircuit<N: Network> {
    public: InnerPublicVariables<N>,
    private: InnerPrivateVariables<N>,
}

impl<N: Network> InnerCircuit<N> {
    pub fn blank() -> Self {
        Self { public: InnerPublicVariables::blank(), private: InnerPrivateVariables::blank() }
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

        let (
            account_encryption_parameters,
            account_signature_parameters,
            record_commitment_parameters,
            value_commitment_parameters,
            transition_id_crh,
            transaction_id_crh,
            transactions_root_crh,
            block_header_root_crh,
            block_hash_crh,
            ledger_root_crh,
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

            let value_commitment_parameters = N::ValueCommitmentGadget::alloc_constant(
                &mut cs.ns(|| "Declare record value commitment parameters"),
                || Ok(N::value_commitment_scheme().clone()),
            )?;

            let transition_id_crh = N::TransitionIDCRHGadget::alloc_constant(
                &mut cs.ns(|| "Declare the transition ID CRH parameters"),
                || Ok(N::transition_id_parameters().crh()),
            )?;

            let transaction_id_crh = N::TransactionIDCRHGadget::alloc_constant(
                &mut cs.ns(|| "Declare the transaction CRH parameters"),
                || Ok(N::transaction_id_parameters().crh()),
            )?;

            let transactions_root_crh = N::TransactionsRootCRHGadget::alloc_constant(
                &mut cs.ns(|| "Declare the transactions root CRH parameters"),
                || Ok(N::transactions_root_parameters().crh()),
            )?;

            let block_header_root_crh = N::BlockHeaderRootCRHGadget::alloc_constant(
                &mut cs.ns(|| "Declare the block header root CRH parameters"),
                || Ok(N::block_header_root_parameters().crh()),
            )?;

            let block_hash_crh =
                N::BlockHashCRHGadget::alloc_constant(&mut cs.ns(|| "Declare the block hash CRH parameters"), || {
                    Ok(N::block_hash_crh().clone())
                })?;

            let ledger_root_crh = N::LedgerRootCRHGadget::alloc_constant(
                &mut cs.ns(|| "Declare the ledger root CRH parameters"),
                || Ok(N::ledger_root_parameters().crh()),
            )?;

            (
                account_encryption_parameters,
                account_signature_parameters,
                record_commitment_parameters,
                value_commitment_parameters,
                transition_id_crh,
                transaction_id_crh,
                transactions_root_crh,
                block_header_root_crh,
                block_hash_crh,
                ledger_root_crh,
            )
        };

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

        // Declare the ledger root.
        let ledger_root = <N::LedgerRootCRHGadget as CRHGadget<_, _>>::OutputGadget::alloc_input(
            &mut cs.ns(|| "Declare the ledger root"),
            || Ok(public.ledger_root()),
        )?;

        // Declare the local transitions root.
        let local_transitions_root = <N::TransactionIDCRHGadget as CRHGadget<_, _>>::OutputGadget::alloc_input(
            &mut cs.ns(|| "Declare the local transitions root"),
            || Ok(public.local_transitions_root()),
        )?;

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

        // Declare the transition signature .
        let signature = <N::AccountSignatureGadget as SignatureGadget<
            N::AccountSignatureScheme,
            N::InnerScalarField,
        >>::SignatureGadget::alloc(&mut cs.ns(|| "Declare the transition signature"), || {
            Ok(&*private.signature)
        })?;

        /* //////////////////////////////////////////////////////////////////////////// */
        /* ///////////////////////////// INPUT RECORDS //////////////////////////////// */
        /* //////////////////////////////////////////////////////////////////////////// */

        let mut input_commitments_bytes = Vec::with_capacity(N::NUM_INPUT_RECORDS * 32);
        let mut input_owners = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        let mut input_values = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        let mut input_program_id_bytes = Vec::with_capacity(N::NUM_INPUT_RECORDS * 32);

        for (i, ((((record, ledger_proof), serial_number), value_commitment), value_commitment_randomness)) in private
            .input_records
            .iter()
            .zip_eq(&private.ledger_proofs)
            .zip_eq(public.serial_numbers())
            .zip_eq(public.input_value_commitments())
            .zip_eq(&private.input_value_commitment_randomness)
            .enumerate()
        {
            let cs = &mut cs.ns(|| format!("Process input record {}", i));

            // Declare record contents
            let (
                given_owner,
                given_is_dummy,
                given_value,
                given_payload,
                given_program_id,
                given_randomizer,
                given_record_view_key,
            ) = {
                let declare_cs = &mut cs.ns(|| "Declare input record");

                // No need to check that commitments, public keys and hashes are in
                // prime order subgroup because the commitment and CRH parameters
                // are trusted, and so when we recompute these, the newly computed
                // values will always be in correct subgroup. If the input cm, pk
                // or hash is incorrect, then it will not match the computed equivalent.

                let given_owner = <N::AccountSignatureGadget as SignatureGadget<
                    N::AccountSignatureScheme,
                    N::InnerScalarField,
                >>::PublicKeyGadget::alloc(
                    &mut declare_cs.ns(|| "given_record_owner"), || Ok(*record.owner())
                )?;

                let given_is_dummy = Boolean::alloc(&mut declare_cs.ns(|| "given_is_dummy"), || Ok(record.is_dummy()))?;

                let given_value = Int64::alloc(&mut declare_cs.ns(|| "given_value"), || Ok(record.value().as_i64()))?;

                // Use an empty payload if the record does not have one.
                let payload = if let Some(payload) = record.payload().clone() { payload } else { Payload::default() };
                let given_payload = UInt8::alloc_vec(&mut declare_cs.ns(|| "given_payload"), &payload.to_bytes_le()?)?;

                // Use an empty program id if the record does not have one.
                let program_id_bytes = if let Some(program_id) = record.program_id() {
                    program_id.to_bytes_le()?
                } else {
                    vec![0u8; N::PROGRAM_ID_SIZE_IN_BYTES]
                };
                let given_program_id = UInt8::alloc_vec(&mut declare_cs.ns(|| "given_program_id"), &program_id_bytes)?;

                let given_randomizer = <N::AccountEncryptionGadget as EncryptionGadget<
                    N::AccountEncryptionScheme,
                    N::InnerScalarField,
                >>::CiphertextRandomizer::alloc(
                    &mut declare_cs.ns(|| "given_randomizer"), || Ok(record.randomizer())
                )?;

                let given_record_view_key = <N::AccountEncryptionGadget as EncryptionGadget<
                    N::AccountEncryptionScheme,
                    N::InnerScalarField,
                >>::SymmetricKeyGadget::alloc(
                    &mut declare_cs.ns(|| "given_record_view_key"),
                    || Ok(*record.record_view_key().clone()),
                )?;

                (
                    given_owner,
                    given_is_dummy,
                    given_value,
                    given_payload,
                    given_program_id,
                    given_randomizer,
                    given_record_view_key,
                )
            };

            // *******************************************************************
            // Check that the record is well-formed.
            // *******************************************************************
            let (commitment, is_dummy) = {
                let commitment_cs = &mut cs.ns(|| "Check that record is well-formed");

                // *******************************************************************
                // Convert the owner, dummy flag, value, payload, program ID, and randomizer into bits.
                // *******************************************************************

                let given_is_dummy_bytes =
                    given_is_dummy.to_bytes(&mut commitment_cs.ns(|| "Convert given_is_dummy to bytes"))?;
                let given_value_bytes =
                    given_value.to_bytes(&mut commitment_cs.ns(|| "Convert given_value to bytes"))?;

                {
                    let given_value_field_elements = given_value_bytes
                        .to_constraint_field(&mut commitment_cs.ns(|| "convert given value to field elements"))?;
                    let given_payload_field_elements = given_payload
                        .to_constraint_field(&mut commitment_cs.ns(|| "convert given payload to field elements"))?;
                    let given_program_id_field_elements = given_program_id
                        .to_constraint_field(&mut commitment_cs.ns(|| "convert given program ID to field elements"))?;

                    // Perform noop safety checks.
                    given_value_field_elements.conditional_enforce_equal(
                        &mut commitment_cs
                            .ns(|| format!("If the input record {} is empty, enforce it has a value of 0", i)),
                        &zero_value_field_elements,
                        &given_is_dummy,
                    )?;
                    given_payload_field_elements.conditional_enforce_equal(
                        &mut commitment_cs
                            .ns(|| format!("If the input record {} is empty, enforce it has an empty payload", i)),
                        &empty_payload_field_elements,
                        &given_is_dummy,
                    )?;
                    given_program_id_field_elements.conditional_enforce_equal(
                        &mut commitment_cs
                            .ns(|| format!("If the input record {} is empty, enforce it has an empty program ID", i)),
                        &empty_program_id_field_elements,
                        &given_is_dummy,
                    )?;

                    // Ensure the program ID matches the declared program ID (conditionally).
                    given_program_id_field_elements.conditional_enforce_equal(
                        &mut commitment_cs.ns(|| format!("Check the {}-th input program ID matches", i)),
                        &program_id_fe,
                        &given_is_dummy.not(),
                    )?;

                    input_program_id_bytes.push(given_program_id.clone());
                }

                // *******************************************************************
                // Compute the record commitment and check that it matches the declared commitment.
                // *******************************************************************

                // TODO (howardwu): CRITICAL - Use given_owner by exposing the FpGadget in the signature trait.
                let owner_fe = FromBytes::read_le(&record.owner().to_bytes_le()?[..])?;
                let given_owner_gadget =
                    FpGadget::alloc(&mut commitment_cs.ns(|| format!("Field element {}", i)), || Ok(&owner_fe))?;

                let encoded_given_value = <N::AccountEncryptionGadget as EncryptionGadget<
                    N::AccountEncryptionScheme,
                    N::InnerScalarField,
                >>::encode_message(
                    &mut commitment_cs.ns(|| format!("encode input value {}", i)),
                    &given_value_bytes,
                )?;

                let encoded_given_payload = <N::AccountEncryptionGadget as EncryptionGadget<
                    N::AccountEncryptionScheme,
                    N::InnerScalarField,
                >>::encode_message(
                    &mut commitment_cs.ns(|| format!("encode input payload {}", i)),
                    &given_payload,
                )?;

                let mut plaintext = Vec::with_capacity(1 + encoded_given_value.len() + encoded_given_payload.len());
                plaintext.push(given_owner_gadget);
                plaintext.extend_from_slice(&encoded_given_value);
                plaintext.extend_from_slice(&encoded_given_payload);

                let ciphertext = account_encryption_parameters.check_encryption_from_symmetric_key(
                    &mut commitment_cs.ns(|| format!("input record {} check_encryption_gadget", i)),
                    &given_record_view_key,
                    &plaintext,
                )?;

                let record_view_key_commitment = account_encryption_parameters.check_symmetric_key_commitment(
                    &mut commitment_cs.ns(|| format!("input record {} check_symmetric_key_commitment", i)),
                    &given_record_view_key,
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
                            .to_bytes(&mut commitment_cs.ns(|| format!("Convert input ciphertext {} to bytes", i)))
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

                let candidate_commitment_bytes =
                    candidate_commitment.to_bytes(&mut commitment_cs.ns(|| "Convert candidate_commitment to bytes"))?;

                input_owners.push(given_owner);
                input_commitments_bytes.extend_from_slice(&candidate_commitment_bytes);
                input_values.push(given_value);

                (candidate_commitment, given_is_dummy)
            };

            // ********************************************************************
            // Check that the serial number is derived correctly.
            // ********************************************************************
            {
                let sn_cs = &mut cs.ns(|| "Check that sn is derived correctly");

                let sk_prf_bits = {
                    let compute_key = N::AccountSignatureGadget::compute_key(
                        &account_signature_parameters,
                        &mut sn_cs.ns(|| "Compute key"),
                        &signature,
                    )?;
                    compute_key.to_bits_le_strict(&mut sn_cs.ns(|| "Compute key to bits"))?
                };

                let sk_prf = Boolean::le_bits_to_fp_var(&mut sn_cs.ns(|| "Bits to FpGadget"), &sk_prf_bits)?;

                let candidate_serial_number = <N::SerialNumberPRFGadget as PRFGadget<
                    N::SerialNumberPRF,
                    N::InnerScalarField,
                >>::check_evaluation_gadget(
                    &mut sn_cs.ns(|| "Compute serial number"),
                    &sk_prf,
                    &vec![commitment.clone()],
                )?;

                let given_serial_number = <N::SerialNumberPRFGadget as PRFGadget<
                    N::SerialNumberPRF,
                    N::InnerScalarField,
                >>::Output::alloc_input(
                    &mut sn_cs.ns(|| format!("Allocate given input serial number {}", i)),
                    || Ok(*serial_number),
                )?;

                candidate_serial_number.enforce_equal(
                    &mut sn_cs.ns(|| format!("Check that the {}-th input serial number is valid", i)),
                    &given_serial_number,
                )?;
            };

            // **********************************************************************************
            // Check that the commitment appears on the ledger or prior transition,
            // i.e., the membership witness is valid with respect to the ledger root.
            // **********************************************************************************
            {
                // Ensure each commitment is either 1) in the ledger, 2) from a prior local transition, or 3) a dummy.
                let ledger_cs = &mut cs.ns(|| "Check ledger proof");

                // Compute the transition ID.
                let transition_inclusion_proof = MerklePathGadget::<_, N::TransitionIDCRHGadget, _>::alloc(
                    &mut ledger_cs.ns(|| "Declare the transition ID inclusion proof"),
                    || Ok(ledger_proof.transition_inclusion_proof()),
                )?;
                let candidate_transition_id = transition_inclusion_proof.calculate_root(
                    &mut ledger_cs.ns(|| "Perform the transition inclusion proof computation"),
                    &transition_id_crh,
                    &commitment,
                )?;

                // Compute the transaction ID.
                let transaction_id_inclusion_proof = MerklePathGadget::<_, N::TransactionIDCRHGadget, _>::alloc(
                    &mut ledger_cs.ns(|| "Declare the transaction ID inclusion proof"),
                    || Ok(ledger_proof.transaction_inclusion_proof()),
                )?;
                let candidate_transaction_id = transaction_id_inclusion_proof.calculate_root(
                    &mut ledger_cs.ns(|| "Perform the transaction ID inclusion proof computation"),
                    &transaction_id_crh,
                    &candidate_transition_id,
                )?;

                // Determine if the commitment is local.
                let is_local = candidate_transaction_id.is_eq(
                    &mut ledger_cs.ns(|| "Check if the local transitions root matches the candidate transaction ID"),
                    &local_transitions_root,
                )?;

                // Determine if the commitment is local or dummy.
                let is_local_or_dummy = Boolean::or(
                    &mut ledger_cs.ns(|| "Determine if the commitment is local or dummy"),
                    &is_local,
                    &is_dummy,
                )?;

                // Compute the transactions root.
                let ledger_transactions_root_inclusion_proof =
                    MerklePathGadget::<_, N::TransactionsRootCRHGadget, _>::alloc(
                        &mut ledger_cs.ns(|| "Declare the ledger transactions root inclusion proof"),
                        || Ok(ledger_proof.transactions_inclusion_proof()),
                    )?;
                let candidate_ledger_transactions_root = ledger_transactions_root_inclusion_proof.calculate_root(
                    &mut ledger_cs.ns(|| "Perform the ledger transactions root inclusion proof computation"),
                    &transactions_root_crh,
                    &candidate_transaction_id,
                )?;

                // Compute the block header root.
                let block_header_root_inclusion_proof = MerklePathGadget::<_, N::BlockHeaderRootCRHGadget, _>::alloc(
                    &mut ledger_cs.ns(|| "Declare the block header root inclusion proof"),
                    || Ok(ledger_proof.block_header_inclusion_proof()),
                )?;
                let candidate_block_header_root = block_header_root_inclusion_proof.calculate_root(
                    &mut ledger_cs.ns(|| "Perform the block header root inclusion proof computation"),
                    &block_header_root_crh,
                    &candidate_ledger_transactions_root,
                )?;

                // Declare the previous block hash.
                let previous_block_hash = UInt8::alloc_vec(
                    &mut ledger_cs.ns(|| "Allocate network id"),
                    &ledger_proof.previous_block_hash().to_bytes_le()?,
                )?;

                // Construct the block hash preimage.
                let mut preimage = Vec::new();
                preimage.extend_from_slice(&previous_block_hash);
                preimage.extend_from_slice(
                    &candidate_block_header_root.to_bytes(&mut ledger_cs.ns(|| "block_header_root"))?,
                );

                // Compute the block hash.
                let candidate_block_hash =
                    block_hash_crh.check_evaluation_gadget(&mut ledger_cs.ns(|| "Compute the block hash"), preimage)?;

                // Ensure the ledger root inclusion proof is valid.
                let ledger_root_inclusion_proof = MerklePathGadget::<_, N::LedgerRootCRHGadget, _>::alloc(
                    &mut ledger_cs.ns(|| "Declare the ledger root inclusion proof"),
                    || Ok(ledger_proof.ledger_root_inclusion_proof()),
                )?;
                ledger_root_inclusion_proof.conditionally_check_membership(
                    &mut ledger_cs.ns(|| "Perform the ledger root inclusion proof check"),
                    &ledger_root_crh,
                    &ledger_root,
                    &candidate_block_hash,
                    &is_local_or_dummy.not(),
                )?;
            }

            // ********************************************************************
            // Check that the input value commitment is derived correctly.
            // ********************************************************************
            {
                let vc_cs = &mut cs.ns(|| "Check that value commitment is derived correctly");

                let value_commitment_randomness_gadget = <N::ValueCommitmentGadget as CommitmentGadget<
                    N::ValueCommitmentScheme,
                    N::InnerScalarField,
                >>::RandomnessGadget::alloc(
                    &mut vc_cs.ns(|| format!("Input value commitment randomness {}", i)),
                    || Ok(value_commitment_randomness),
                )?;

                let given_value_commitment_gadget = <N::ValueCommitmentGadget as CommitmentGadget<
                    N::ValueCommitmentScheme,
                    N::InnerScalarField,
                >>::OutputGadget::alloc(
                    &mut vc_cs.ns(|| format!("Input value commitment {}", i)),
                    || Ok(value_commitment),
                )?;

                let value_bytes =
                    UInt8::alloc_vec(vc_cs.ns(|| format!("Input value bytes {}", i)), &record.value().to_bytes_le()?)?;

                let candidate_value_commitment_gadget = value_commitment_parameters.check_commitment_gadget(
                    &mut vc_cs.ns(|| format!("Compute input value commitment {}", i)),
                    &value_bytes,
                    &value_commitment_randomness_gadget,
                )?;

                candidate_value_commitment_gadget.enforce_equal(
                    &mut vc_cs.ns(|| format!("Check that the {}-th input value commitment is valid", i)),
                    &given_value_commitment_gadget,
                )?;
            }
        }
        // ********************************************************************

        // *******************************************************************
        // Check that the signature is valid.
        // *******************************************************************
        {
            let signature_cs = &mut cs.ns(|| "Check that the signature is valid");

            // Enforce that the input owners are the same address.
            let mut current_owner = &input_owners[0];
            for (i, next_owner) in input_owners.iter().take(N::NUM_INPUT_RECORDS).skip(1).enumerate() {
                // Enforce the owners are equal.
                current_owner.enforce_equal(signature_cs.ns(|| format!("check_owners_match_{}", i)), next_owner)?;
                // Update the current owner.
                current_owner = next_owner;
            }

            let mut signature_message = Vec::new();
            signature_message.extend_from_slice(&input_commitments_bytes);
            signature_message.extend_from_slice(&input_program_id_bytes[0]);
            // signature_message.extend_from_slice(&inputs_digest);
            // signature_message.extend_from_slice(&fee);

            let signature_verification = account_signature_parameters.verify(
                signature_cs.ns(|| "signature_verify"),
                &input_owners[0],
                &signature_message,
                &signature,
            )?;

            signature_verification.enforce_equal(signature_cs.ns(|| "check_verification"), &Boolean::constant(true))?;
        }

        /* //////////////////////////////////////////////////////////////////////////// */
        /* //////////////////////////// OUTPUT RECORDS //////////////////////////////// */
        /* //////////////////////////////////////////////////////////////////////////// */

        let mut output_values = Vec::with_capacity(N::NUM_OUTPUT_RECORDS);

        for (j, ((((record, encryption_randomness), commitment), value_commitment), value_commitment_randomness)) in
            private
                .output_records
                .iter()
                .zip_eq(&private.encryption_randomness)
                .zip_eq(public.commitments())
                .zip_eq(public.output_value_commitments())
                .zip_eq(&private.output_value_commitment_randomness)
                .enumerate()
        {
            let cs = &mut cs.ns(|| format!("Process output record {}", j));

            let (given_owner, given_is_dummy, given_value, given_payload, given_program_id, given_randomizer) = {
                let declare_cs = &mut cs.ns(|| "Declare output record");

                let given_owner = <N::AccountEncryptionGadget as EncryptionGadget<
                    N::AccountEncryptionScheme,
                    N::InnerScalarField,
                >>::PublicKeyGadget::alloc(
                    &mut declare_cs.ns(|| "given_record_owner"), || Ok(*record.owner())
                )?;

                let given_is_dummy = Boolean::alloc(&mut declare_cs.ns(|| "given_is_dummy"), || Ok(record.is_dummy()))?;

                let given_value = Int64::alloc(&mut declare_cs.ns(|| "given_value"), || Ok(record.value().as_i64()))?;

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

                (given_owner, given_is_dummy, given_value, given_payload, given_program_id, given_randomizer)
            };
            // ********************************************************************

            // *******************************************************************
            // Check that the record is well-formed.
            // *******************************************************************
            {
                let commitment_cs = &mut cs.ns(|| "Check that record is well-formed");

                // *******************************************************************
                // Convert the owner, dummy flag, value, payload, program ID, and randomizer into bits.
                // *******************************************************************

                let given_is_dummy_bytes =
                    given_is_dummy.to_bytes(&mut commitment_cs.ns(|| "Convert given_is_dummy to bytes"))?;
                let given_value_bytes =
                    given_value.to_bytes(&mut commitment_cs.ns(|| "Convert given_value to bytes"))?;

                {
                    let given_value_field_elements = given_value_bytes
                        .to_constraint_field(&mut commitment_cs.ns(|| "convert given value to field elements"))?;
                    let given_payload_field_elements = given_payload
                        .to_constraint_field(&mut commitment_cs.ns(|| "convert given payload to field elements"))?;
                    let given_program_id_field_elements = given_program_id
                        .to_constraint_field(&mut commitment_cs.ns(|| "convert given program ID to field elements"))?;

                    // Perform noop safety checks.
                    given_value_field_elements.conditional_enforce_equal(
                        &mut commitment_cs
                            .ns(|| format!("If the output record {} is empty, enforce it has a value of 0", j)),
                        &zero_value_field_elements,
                        &given_is_dummy,
                    )?;
                    given_payload_field_elements.conditional_enforce_equal(
                        &mut commitment_cs
                            .ns(|| format!("If the output record {} is empty, enforce it has an empty payload", j)),
                        &empty_payload_field_elements,
                        &given_is_dummy,
                    )?;
                    given_program_id_field_elements.conditional_enforce_equal(
                        &mut commitment_cs
                            .ns(|| format!("If the output record {} is empty, enforce it has an empty program ID", j)),
                        &empty_program_id_field_elements,
                        &given_is_dummy,
                    )?;

                    // Ensure the program ID matches the declared program ID (conditionally).
                    given_program_id_field_elements.conditional_enforce_equal(
                        &mut commitment_cs.ns(|| format!("Check the {}-th output program ID matches", j)),
                        &program_id_fe,
                        &given_is_dummy.not(),
                    )?;
                }

                // *******************************************************************
                // Check that the record ciphertext and commitment are well-formed.
                // *******************************************************************

                // TODO (howardwu): CRITICAL - Use given_owner by exposing the FpGadget in the signature trait.
                let owner_fe = FromBytes::read_le(&record.owner().to_bytes_le()?[..])?;
                let given_owner_gadget =
                    FpGadget::alloc(&mut commitment_cs.ns(|| format!("Field element {}", j)), || Ok(&owner_fe))?;

                let encoded_given_value = <N::AccountEncryptionGadget as EncryptionGadget<
                    N::AccountEncryptionScheme,
                    N::InnerScalarField,
                >>::encode_message(
                    &mut commitment_cs.ns(|| format!("encode input value {}", j)),
                    &given_value_bytes,
                )?;

                let encoded_given_payload = <N::AccountEncryptionGadget as EncryptionGadget<
                    N::AccountEncryptionScheme,
                    N::InnerScalarField,
                >>::encode_message(
                    &mut commitment_cs.ns(|| format!("encode input payload {}", j)),
                    &given_payload,
                )?;

                let mut plaintext = Vec::with_capacity(1 + encoded_given_value.len() + encoded_given_payload.len());
                plaintext.push(given_owner_gadget);
                plaintext.extend_from_slice(&encoded_given_value);
                plaintext.extend_from_slice(&encoded_given_payload);

                let encryption_randomness = <N::AccountEncryptionGadget as EncryptionGadget<
                    N::AccountEncryptionScheme,
                    N::InnerScalarField,
                >>::ScalarRandomnessGadget::alloc(
                    &mut commitment_cs.ns(|| format!("output record {} encryption_randomness", j)),
                    || Ok(encryption_randomness),
                )?;

                let (candidate_ciphertext_randomizer, ciphertext, record_view_key) = account_encryption_parameters
                    .check_encryption_from_scalar_randomness(
                        &mut commitment_cs.ns(|| format!("output record {} check_encryption_gadget", j)),
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
                    &mut commitment_cs.ns(|| format!("output record {} check_symmetric_key_commitment", j)),
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
                    &mut commitment_cs.ns(|| format!("Allocate given output commitment {}", j)),
                    || Ok(*commitment),
                )?;

                candidate_commitment.enforce_equal(
                    &mut commitment_cs.ns(|| format!("Check that the {}-th output commitment is valid", j)),
                    &given_commitment,
                )?;

                output_values.push(given_value);
            };

            // ********************************************************************
            // Check that the ouput value commitment is derived correctly.
            // ********************************************************************
            {
                let vc_cs = &mut cs.ns(|| "Check that value commitment is derived correctly");

                let value_commitment_randomness_gadget = <N::ValueCommitmentGadget as CommitmentGadget<
                    N::ValueCommitmentScheme,
                    N::InnerScalarField,
                >>::RandomnessGadget::alloc(
                    &mut vc_cs.ns(|| format!("Output value commitment randomness {}", j)),
                    || Ok(value_commitment_randomness),
                )?;

                let given_value_commitment_gadget = <N::ValueCommitmentGadget as CommitmentGadget<
                    N::ValueCommitmentScheme,
                    N::InnerScalarField,
                >>::OutputGadget::alloc(
                    &mut vc_cs.ns(|| format!("Output value commitment {}", j)),
                    || Ok(value_commitment),
                )?;

                let value_bytes =
                    UInt8::alloc_vec(vc_cs.ns(|| format!("Output value bytes {}", j)), &record.value().to_bytes_le()?)?;

                let candidate_value_commitment_gadget = value_commitment_parameters.check_commitment_gadget(
                    &mut vc_cs.ns(|| format!("Compute output value commitment {}", j)),
                    &value_bytes,
                    &value_commitment_randomness_gadget,
                )?;

                candidate_value_commitment_gadget.enforce_equal(
                    &mut vc_cs.ns(|| format!("Check that the {}-th output value commitment is valid", j)),
                    &given_value_commitment_gadget,
                )?;
            }
        }
        // *******************************************************************

        // *******************************************************************
        // Check that the value balance is valid.
        // *******************************************************************
        {
            let mut cs = cs.ns(|| "Check that the value balance is valid.");

            let mut candidate_value_balance = Int64::zero();

            for (i, input_value) in input_values.iter().enumerate() {
                // Enforce the record value has positive value that is less than 2^63.
                for (j, bit) in input_value.to_bits_be()[0..2].iter().enumerate() {
                    bit.enforce_equal(
                        cs.ns(|| format!("enforce input {} bit {} is 0", i, j)),
                        &Boolean::constant(false),
                    )?;
                }

                candidate_value_balance = candidate_value_balance
                    .add(cs.ns(|| format!("add input record {} value", i)), input_value)
                    .unwrap();
            }

            for (j, output_value) in output_values.iter().enumerate() {
                // Enforce the record value has positive value that is less than 2^63.
                for (k, bit) in output_value.to_bits_be()[0..2].iter().enumerate() {
                    bit.enforce_equal(
                        cs.ns(|| format!("enforce output {} bit {} is 0", j, k)),
                        &Boolean::constant(false),
                    )?;
                }

                candidate_value_balance = candidate_value_balance
                    .sub(cs.ns(|| format!("sub output record {} value", j)), output_value)
                    .unwrap();
            }

            let candidate_value_balance_bytes = candidate_value_balance.to_bytes(cs.ns(|| "value_balance_bytes"))?;
            let candidate_value_balance_field_elements = candidate_value_balance_bytes
                .to_constraint_field(&mut cs.ns(|| "convert candidate value balance to field elements"))?;

            let given_value_balance_bytes = UInt8::alloc_input_vec_le(
                &mut cs.ns(|| "Allocate given_value_balance"),
                &public.value_balance().to_bytes_le()?,
            )?;
            let given_value_balance_field_elements = given_value_balance_bytes
                .to_constraint_field(&mut cs.ns(|| "convert given value balance to field elements"))?;

            candidate_value_balance_field_elements.enforce_equal(
                &mut cs.ns(|| "enforce the value balance is equal"),
                &given_value_balance_field_elements,
            )?;
        };

        // *******************************************************************

        // *******************************************************************
        // Check that the value balance is valid by verifying the value balance commitment.
        // *******************************************************************
        {
            let mut cs = cs.ns(|| "Check that the value balance commitment is valid.");

            let transition_id = Transition::<N>::compute_transition_id(public.serial_numbers(), public.commitments())?;

            // TODO (raychu86): Confirm if we need to do this operation in the gadget world.
            let (c, partial_combined_commitments, zero_commitment, blinded_commitment) = public
                .value_balance_commitment()
                .gadget_verification_setup(
                    public.input_value_commitments(),
                    public.output_value_commitments(),
                    &transition_id.to_bytes_le()?,
                )
                .unwrap();

            let c_gadget = <N::ValueCommitmentGadget as CommitmentGadget<
                N::ValueCommitmentScheme,
                N::InnerScalarField,
            >>::RandomnessGadget::alloc(&mut cs.ns(|| "c"), || Ok(&c))?;

            let partial_combined_commitments_gadget = <N::ValueCommitmentGadget as CommitmentGadget<
                N::ValueCommitmentScheme,
                N::InnerScalarField,
            >>::OutputGadget::alloc(
                &mut cs.ns(|| "Partially combined commitments"),
                || Ok(partial_combined_commitments),
            )?;

            let zero_commitment_gadget = <N::ValueCommitmentGadget as CommitmentGadget<
                N::ValueCommitmentScheme,
                N::InnerScalarField,
            >>::OutputGadget::alloc(
                &mut cs.ns(|| "Zero commitment gadget"), || Ok(zero_commitment)
            )?;

            let blinded_commitment_gadget = <N::ValueCommitmentGadget as CommitmentGadget<
                N::ValueCommitmentScheme,
                N::InnerScalarField,
            >>::OutputGadget::alloc(
                &mut cs.ns(|| "Blinding commitment gadget"), || Ok(blinded_commitment)
            )?;

            let value_balance_bytes = UInt8::alloc_vec(
                cs.ns(|| "value_balance_bytes"),
                &(public.value_balance().0.abs() as u64).to_le_bytes(),
            )?;

            let is_negative = Boolean::alloc(&mut cs.ns(|| "Value balance is negative"), || {
                Ok(public.value_balance().is_negative())
            })?;

            let value_balance_comm = ValueBalanceCommitmentGadget::<N>::check_commitment_without_randomness_gadget(
                &mut cs.ns(|| "Commitment on value balance without randomness"),
                &value_commitment_parameters,
                &value_balance_bytes,
            )?;

            ValueBalanceCommitmentGadget::<N>::check_value_balance_commitment_gadget(
                &mut cs.ns(|| "Verify value balance commitment"),
                &partial_combined_commitments_gadget,
                &value_balance_comm,
                &is_negative,
                &c_gadget,
                &zero_commitment_gadget,
                &blinded_commitment_gadget,
            )?;
        }

        Ok(())
    }
}
