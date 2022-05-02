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

use crate::{InputPrivateVariables, InputPublicVariables, Network, Payload};
use snarkvm_algorithms::traits::*;
use snarkvm_gadgets::{
    algorithms::merkle_tree::merkle_path::MerklePathGadget,
    bits::{Boolean, ToBytesGadget},
    integers::uint::UInt8,
    traits::{
        algorithms::{CRHGadget, CommitmentGadget, EncryptionGadget, PRFGadget, SignatureGadget},
        alloc::AllocGadget,
        eq::{ConditionalEqGadget, EqGadget},
    },
    FpGadget,
    ToBitsLEGadget,
    ToConstraintFieldGadget,
};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSynthesizer, ConstraintSystem};
use snarkvm_utilities::{FromBytes, ToBytes};

#[derive(Clone)]
pub struct InputCircuit<N: Network> {
    public: InputPublicVariables<N>,
    private: InputPrivateVariables<N>,
}

impl<N: Network> InputCircuit<N> {
    pub fn blank() -> Self {
        Self { public: InputPublicVariables::blank(), private: InputPrivateVariables::blank() }
    }

    pub fn new(public: InputPublicVariables<N>, private: InputPrivateVariables<N>) -> Self {
        Self { public, private }
    }
}

impl<N: Network> ConstraintSynthesizer<N::InnerScalarField> for InputCircuit<N> {
    fn generate_constraints<CS: ConstraintSystem<N::InnerScalarField>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let public = &self.public;
        let private = &self.private;

        let serial_number = public.serial_number();
        let value_commitment = public.input_value_commitment();

        let record = &private.input_record;
        let ledger_proof = &private.ledger_proof;
        let value_commitment_randomness = &private.input_value_commitment_randomness;

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

        // Declare the transition signature.
        let signature = <N::AccountSignatureGadget as SignatureGadget<
            N::AccountSignatureScheme,
            N::InnerScalarField,
        >>::SignatureGadget::alloc(&mut cs.ns(|| "Declare the transition signature"), || {
            Ok(&*private.signature)
        })?;

        let (
            account_encryption_parameters,
            account_signature_parameters,
            record_commitment_parameters,
            value_commitment_parameters,
            transition_id_crh,
            transition_id_two_to_one_crh,
            transaction_id_crh,
            transaction_id_two_to_one_crh,
            transactions_root_crh,
            transactions_root_two_to_one_crh,
            block_header_root_crh,
            block_header_root_two_to_one_crh,
            block_hash_crh,
            ledger_root_crh,
            ledger_root_two_to_one_crh,
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
                || Ok(N::transition_id_parameters().leaf_crh()),
            )?;

            let transition_id_two_to_one_crh = N::TransitionIDTwoToOneCRHGadget::alloc_constant(
                &mut cs.ns(|| "Declare the transition ID two to one CRH parameters"),
                || Ok(N::transition_id_parameters().two_to_one_crh()),
            )?;

            let transaction_id_crh = N::TransactionIDCRHGadget::alloc_constant(
                &mut cs.ns(|| "Declare the transaction CRH parameters"),
                || Ok(N::transaction_id_parameters().leaf_crh()),
            )?;

            let transaction_id_two_to_one_crh = N::TransactionIDTwoToOneCRHGadget::alloc_constant(
                &mut cs.ns(|| "Declare the transaction two to one CRH parameters"),
                || Ok(N::transaction_id_parameters().two_to_one_crh()),
            )?;

            let transactions_root_crh = N::TransactionsRootCRHGadget::alloc_constant(
                &mut cs.ns(|| "Declare the transactions root CRH parameters"),
                || Ok(N::transactions_root_parameters().leaf_crh()),
            )?;

            let transactions_root_two_to_one_crh = N::TransactionsRootTwoToOneCRHGadget::alloc_constant(
                &mut cs.ns(|| "Declare the transactions root two to one CRH parameters"),
                || Ok(N::transactions_root_parameters().two_to_one_crh()),
            )?;

            let block_header_root_crh = N::BlockHeaderRootCRHGadget::alloc_constant(
                &mut cs.ns(|| "Declare the block header root CRH parameters"),
                || Ok(N::block_header_root_parameters().leaf_crh()),
            )?;

            let block_header_root_two_to_one_crh = N::BlockHeaderRootTwoToOneCRHGadget::alloc_constant(
                &mut cs.ns(|| "Declare the block header root two to one CRH parameters"),
                || Ok(N::block_header_root_parameters().two_to_one_crh()),
            )?;

            let block_hash_crh =
                N::BlockHashCRHGadget::alloc_constant(&mut cs.ns(|| "Declare the block hash CRH parameters"), || {
                    Ok(N::block_hash_crh().clone())
                })?;

            let ledger_root_crh = N::LedgerRootCRHGadget::alloc_constant(
                &mut cs.ns(|| "Declare the ledger root CRH parameters"),
                || Ok(N::ledger_root_parameters().leaf_crh()),
            )?;

            let ledger_root_two_to_one_crh = N::LedgerRootTwoToOneCRHGadget::alloc_constant(
                &mut cs.ns(|| "Declare the ledger root two to one CRH parameters"),
                || Ok(N::ledger_root_parameters().two_to_one_crh()),
            )?;

            (
                account_encryption_parameters,
                account_signature_parameters,
                record_commitment_parameters,
                value_commitment_parameters,
                transition_id_crh,
                transition_id_two_to_one_crh,
                transaction_id_crh,
                transaction_id_two_to_one_crh,
                transactions_root_crh,
                transactions_root_two_to_one_crh,
                block_header_root_crh,
                block_header_root_two_to_one_crh,
                block_hash_crh,
                ledger_root_crh,
                ledger_root_two_to_one_crh,
            )
        };

        // Declare record contents
        let (
            given_owner,
            given_is_dummy,
            given_value_bytes,
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

            let given_value_bytes =
                UInt8::alloc_vec(&mut declare_cs.ns(|| "given_value"), &record.value().to_bytes_le()?)?;

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
                given_value_bytes,
                given_payload,
                given_program_id,
                given_randomizer,
                given_record_view_key,
            )
        };

        // *******************************************************************
        // Check that the record is well-formed.
        // *******************************************************************
        let (commitment, value_bytes, is_dummy, candidate_commitment_bytes, input_program_id_bytes) = {
            let commitment_cs = &mut cs.ns(|| "Check that record is well-formed");

            // *******************************************************************
            // Convert the owner, dummy flag, value, payload, program ID, and randomizer into bits.
            // *******************************************************************

            let given_is_dummy_bytes =
                given_is_dummy.to_bytes(&mut commitment_cs.ns(|| "Convert given_is_dummy to bytes"))?;

            let input_program_id_bytes = {
                let given_value_field_elements = given_value_bytes
                    .to_constraint_field(&mut commitment_cs.ns(|| "convert given value to field elements"))?;
                let given_payload_field_elements = given_payload
                    .to_constraint_field(&mut commitment_cs.ns(|| "convert given payload to field elements"))?;
                let given_program_id_field_elements = given_program_id
                    .to_constraint_field(&mut commitment_cs.ns(|| "convert given program ID to field elements"))?;

                // Perform noop safety checks.
                given_value_field_elements.conditional_enforce_equal(
                    &mut commitment_cs.ns(|| "If the input record is empty, enforce it has a value of 0"),
                    &zero_value_field_elements,
                    &given_is_dummy,
                )?;
                given_payload_field_elements.conditional_enforce_equal(
                    &mut commitment_cs.ns(|| "If the input record is empty, enforce it has an empty payload"),
                    &empty_payload_field_elements,
                    &given_is_dummy,
                )?;
                given_program_id_field_elements.conditional_enforce_equal(
                    &mut commitment_cs.ns(|| "If the input record is empty, enforce it has an empty program ID"),
                    &empty_program_id_field_elements,
                    &given_is_dummy,
                )?;

                // Ensure the program ID matches the declared program ID (conditionally).
                given_program_id_field_elements.conditional_enforce_equal(
                    &mut commitment_cs.ns(|| "Check the input program ID matches"),
                    &program_id_fe,
                    &given_is_dummy.not(),
                )?;

                // input_program_id_bytes.push(given_program_id.clone());

                given_program_id.clone()
            };

            // *******************************************************************
            // Compute the record commitment and check that it matches the declared commitment.
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

            let ciphertext = account_encryption_parameters.check_encryption_from_symmetric_key(
                &mut commitment_cs.ns(|| "input record check_encryption_gadget"),
                &given_record_view_key,
                &plaintext,
            )?;

            let record_view_key_commitment = account_encryption_parameters.check_symmetric_key_commitment(
                &mut commitment_cs.ns(|| "input record check_symmetric_key_commitment"),
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

            (
                candidate_commitment,
                given_value_bytes,
                given_is_dummy,
                candidate_commitment_bytes,
                input_program_id_bytes,
            )
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

            let given_serial_number =
                <N::SerialNumberPRFGadget as PRFGadget<N::SerialNumberPRF, N::InnerScalarField>>::Output::alloc_input(
                    &mut sn_cs.ns(|| "Allocate given input serial number"),
                    || Ok(*serial_number),
                )?;

            candidate_serial_number.enforce_equal(
                &mut sn_cs.ns(|| "Check that the-th input serial number is valid"),
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
            let transition_inclusion_proof =
                MerklePathGadget::<_, N::TransitionIDCRHGadget, N::TransitionIDTwoToOneCRHGadget, _>::alloc(
                    &mut ledger_cs.ns(|| "Declare the transition ID inclusion proof"),
                    || Ok(ledger_proof.transition_inclusion_proof()),
                )?;
            let candidate_transition_id = transition_inclusion_proof.calculate_root(
                &mut ledger_cs.ns(|| "Perform the transition inclusion proof computation"),
                &transition_id_crh,
                &transition_id_two_to_one_crh,
                &commitment,
            )?;

            // Compute the transaction ID.
            let transaction_id_inclusion_proof =
                MerklePathGadget::<_, N::TransactionIDCRHGadget, N::TransactionIDTwoToOneCRHGadget, _>::alloc(
                    &mut ledger_cs.ns(|| "Declare the transaction ID inclusion proof"),
                    || Ok(ledger_proof.transaction_inclusion_proof()),
                )?;
            let candidate_transaction_id = transaction_id_inclusion_proof.calculate_root(
                &mut ledger_cs.ns(|| "Perform the transaction ID inclusion proof computation"),
                &transaction_id_crh,
                &transaction_id_two_to_one_crh,
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
                MerklePathGadget::<_, N::TransactionsRootCRHGadget, N::TransactionsRootTwoToOneCRHGadget, _>::alloc(
                    &mut ledger_cs.ns(|| "Declare the ledger transactions root inclusion proof"),
                    || Ok(ledger_proof.transactions_inclusion_proof()),
                )?;
            let candidate_ledger_transactions_root = ledger_transactions_root_inclusion_proof.calculate_root(
                &mut ledger_cs.ns(|| "Perform the ledger transactions root inclusion proof computation"),
                &transactions_root_crh,
                &transactions_root_two_to_one_crh,
                &candidate_transaction_id,
            )?;

            // Compute the block header root.
            let block_header_root_inclusion_proof =
                MerklePathGadget::<_, N::BlockHeaderRootCRHGadget, N::BlockHeaderRootTwoToOneCRHGadget, _>::alloc(
                    &mut ledger_cs.ns(|| "Declare the block header root inclusion proof"),
                    || Ok(ledger_proof.block_header_inclusion_proof()),
                )?;
            let candidate_block_header_root = block_header_root_inclusion_proof.calculate_root(
                &mut ledger_cs.ns(|| "Perform the block header root inclusion proof computation"),
                &block_header_root_crh,
                &block_header_root_two_to_one_crh,
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
            preimage
                .extend_from_slice(&candidate_block_header_root.to_bytes(&mut ledger_cs.ns(|| "block_header_root"))?);

            // Compute the block hash.
            let candidate_block_hash =
                block_hash_crh.check_evaluation_gadget(&mut ledger_cs.ns(|| "Compute the block hash"), preimage)?;

            // Ensure the ledger root inclusion proof is valid.
            let ledger_root_inclusion_proof =
                MerklePathGadget::<_, N::LedgerRootCRHGadget, N::LedgerRootTwoToOneCRHGadget, _>::alloc(
                    &mut ledger_cs.ns(|| "Declare the ledger root inclusion proof"),
                    || Ok(ledger_proof.ledger_root_inclusion_proof()),
                )?;
            ledger_root_inclusion_proof.conditionally_check_membership(
                &mut ledger_cs.ns(|| "Perform the ledger root inclusion proof check"),
                &ledger_root_crh,
                &ledger_root_two_to_one_crh,
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
                &mut vc_cs.ns(|| "Input value commitment randomness"),
                || Ok(value_commitment_randomness),
            )?;

            let given_value_commitment_gadget = <N::ValueCommitmentGadget as CommitmentGadget<
                N::ValueCommitmentScheme,
                N::InnerScalarField,
            >>::OutputGadget::alloc_input(
                &mut vc_cs.ns(|| "Input value commitment"),
                || Ok(**value_commitment),
            )?;

            let candidate_value_commitment_gadget = value_commitment_parameters.check_commitment_gadget(
                &mut vc_cs.ns(|| "Compute input value commitment"),
                &value_bytes,
                &value_commitment_randomness_gadget,
            )?;

            candidate_value_commitment_gadget.enforce_equal(
                &mut vc_cs.ns(|| "Check that the-th input value commitment is valid"),
                &given_value_commitment_gadget,
            )?;
        }

        // ********************************************************************

        // *******************************************************************
        // Check that the signature is valid.
        // *******************************************************************
        {
            let signature_cs = &mut cs.ns(|| "Check that the signature is valid");

            let mut signature_message = Vec::new();
            signature_message.extend_from_slice(&candidate_commitment_bytes);
            signature_message.extend_from_slice(&input_program_id_bytes);

            let signature_message = signature_message.to_bits_le(signature_cs.ns(|| "convert message to bits"))?;

            let signature_verification = account_signature_parameters.verify(
                signature_cs.ns(|| "signature_verify"),
                &given_owner,
                &signature_message,
                &signature,
            )?;

            signature_verification.enforce_equal(signature_cs.ns(|| "check_verification"), &Boolean::constant(true))?;
        }

        Ok(())
    }
}
