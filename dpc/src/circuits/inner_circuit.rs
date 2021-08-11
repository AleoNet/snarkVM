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

use crate::{InnerPrivateVariables, InnerPublicVariables, Parameters, Payload, RecordScheme};
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
use snarkvm_utilities::ToBytes;

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"))]
pub struct InnerCircuit<C: Parameters> {
    public: InnerPublicVariables<C>,
    private: InnerPrivateVariables<C>,
}

impl<C: Parameters> InnerCircuit<C> {
    pub fn blank() -> Self {
        Self {
            public: InnerPublicVariables::blank(),
            private: InnerPrivateVariables::blank(),
        }
    }

    pub fn new(public: InnerPublicVariables<C>, private: InnerPrivateVariables<C>) -> Self {
        Self { public, private }
    }
}

impl<C: Parameters> ConstraintSynthesizer<C::InnerScalarField> for InnerCircuit<C> {
    fn generate_constraints<CS: ConstraintSystem<C::InnerScalarField>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        execute_inner_circuit::<C, CS>(cs, &self.public, &self.private)
    }
}

pub fn execute_inner_circuit<C: Parameters, CS: ConstraintSystem<C::InnerScalarField>>(
    cs: &mut CS,
    public: &InnerPublicVariables<C>,
    private: &InnerPrivateVariables<C>,
) -> Result<(), SynthesisError> {
    // In the inner circuit, these two variables must be allocated as public inputs.
    debug_assert!(public.program_commitment.is_some());
    debug_assert!(public.local_data_root.is_some());

    let (
        account_commitment_parameters,
        account_encryption_parameters,
        account_signature_parameters,
        record_commitment_parameters,
        encrypted_record_crh,
        program_commitment_parameters,
        local_data_crh,
        local_data_commitment_parameters,
        serial_number_nonce_crh,
        record_commitment_tree_parameters,
    ) = {
        let cs = &mut cs.ns(|| "Declare parameters");

        let account_commitment_parameters =
            C::AccountCommitmentGadget::alloc_constant(&mut cs.ns(|| "Declare account commitment parameters"), || {
                Ok(C::account_commitment_scheme().clone())
            })?;

        let account_encryption_parameters =
            C::AccountEncryptionGadget::alloc_constant(&mut cs.ns(|| "Declare account encryption parameters"), || {
                Ok(C::account_encryption_scheme().clone())
            })?;

        let account_signature_parameters =
            C::AccountSignatureGadget::alloc_constant(&mut cs.ns(|| "Declare account signature parameters"), || {
                Ok(C::account_signature_scheme().clone())
            })?;

        let record_commitment_parameters =
            C::RecordCommitmentGadget::alloc_constant(&mut cs.ns(|| "Declare record commitment parameters"), || {
                Ok(C::record_commitment_scheme().clone())
            })?;

        let encrypted_record_crh_parameters = C::EncryptedRecordCRHGadget::alloc_constant(
            &mut cs.ns(|| "Declare record ciphertext CRH parameters"),
            || Ok(C::encrypted_record_crh().clone()),
        )?;

        let program_commitment_parameters =
            C::ProgramCommitmentGadget::alloc_constant(&mut cs.ns(|| "Declare program commitment parameters"), || {
                Ok(C::program_commitment_scheme().clone())
            })?;

        let local_data_crh_parameters =
            C::LocalDataCRHGadget::alloc_constant(&mut cs.ns(|| "Declare local data CRH parameters"), || {
                Ok(C::local_data_crh().clone())
            })?;

        let local_data_commitment_parameters = C::LocalDataCommitmentGadget::alloc_constant(
            &mut cs.ns(|| "Declare local data commitment parameters"),
            || Ok(C::local_data_commitment_scheme().clone()),
        )?;

        let serial_number_nonce_crh_parameters = C::SerialNumberNonceCRHGadget::alloc_constant(
            &mut cs.ns(|| "Declare serial number nonce CRH parameters"),
            || Ok(C::serial_number_nonce_crh().clone()),
        )?;

        let record_commitment_tree_parameters =
            C::RecordCommitmentTreeCRHGadget::alloc_constant(&mut cs.ns(|| "Declare ledger parameters"), || {
                Ok(C::record_commitment_tree_parameters().crh())
            })?;

        (
            account_commitment_parameters,
            account_encryption_parameters,
            account_signature_parameters,
            record_commitment_parameters,
            encrypted_record_crh_parameters,
            program_commitment_parameters,
            local_data_crh_parameters,
            local_data_commitment_parameters,
            serial_number_nonce_crh_parameters,
            record_commitment_tree_parameters,
        )
    };

    // Declares a constant for a 0 value in a record.
    let zero_value = UInt8::constant_vec(&(0u64).to_bytes_le()?);
    // Declares a constant for an empty payload in a record.
    let empty_payload = UInt8::constant_vec(&Payload::default().to_bytes_le()?);

    let digest_gadget = <C::RecordCommitmentTreeCRHGadget as CRHGadget<_, _>>::OutputGadget::alloc_input(
        &mut cs.ns(|| "Declare ledger digest"),
        || Ok(public.ledger_digest),
    )?;

    let mut old_serial_numbers_gadgets = Vec::with_capacity(private.input_records.len());
    let mut old_serial_numbers_bytes_gadgets = Vec::with_capacity(private.input_records.len() * 32); // Serial numbers are 32 bytes
    let mut old_record_commitments_gadgets = Vec::with_capacity(private.input_records.len());
    let mut old_program_ids_gadgets = Vec::with_capacity(private.input_records.len());

    for (i, (((record, witness), compute_key), given_serial_number)) in private
        .input_records
        .iter()
        .zip(&private.input_witnesses)
        .zip(&private.compute_keys)
        .zip(&public.kernel.serial_numbers)
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
            given_serial_number_nonce_bytes,
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
            let given_owner = <C::AccountEncryptionGadget as EncryptionGadget<
                C::AccountEncryptionScheme,
                C::InnerScalarField,
            >>::PublicKeyGadget::alloc(
                &mut declare_cs.ns(|| "given_record_owner"),
                || Ok(record.owner().to_encryption_key()),
            )?;

            let given_is_dummy = Boolean::alloc(&mut declare_cs.ns(|| "given_is_dummy"), || Ok(record.is_dummy()))?;

            let given_value = UInt8::alloc_vec(&mut declare_cs.ns(|| "given_value"), &record.value().to_bytes_le()?)?;

            let given_payload =
                UInt8::alloc_vec(&mut declare_cs.ns(|| "given_payload"), &record.payload().to_bytes_le()?)?;

            let given_serial_number_nonce_bytes = UInt8::alloc_vec(
                &mut declare_cs.ns(|| "given_serial_number_nonce_bytes"),
                &record.serial_number_nonce().to_bytes_le()?,
            )?;

            let given_commitment = <C::RecordCommitmentGadget as CommitmentGadget<
                C::RecordCommitmentScheme,
                C::InnerScalarField,
            >>::OutputGadget::alloc(
                &mut declare_cs.ns(|| "given_commitment"), || Ok(record.commitment())
            )?;
            old_record_commitments_gadgets.push(given_commitment.clone());

            let given_commitment_randomness = <C::RecordCommitmentGadget as CommitmentGadget<
                C::RecordCommitmentScheme,
                C::InnerScalarField,
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
                given_serial_number_nonce_bytes,
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

            let witness_gadget = MerklePathGadget::<_, C::RecordCommitmentTreeCRHGadget, _>::alloc(
                &mut witness_cs.ns(|| "Declare membership witness"),
                || Ok(witness),
            )?;

            witness_gadget.conditionally_check_membership(
                &mut witness_cs.ns(|| "Perform ledger membership witness check"),
                &record_commitment_tree_parameters,
                &digest_gadget,
                &given_commitment,
                &given_is_dummy.not(),
            )?;
        }
        // ********************************************************************

        // ********************************************************************
        // Check that the account address and private key form a valid key
        // pair.
        // ********************************************************************

        let (sk_prf, pk_sig) = {
            // Declare variables for account contents.
            let account_cs = &mut cs.ns(|| "Check account");

            // Allocate the account private key.
            let (pk_sig, sk_prf, r_pk) = {
                let pk_sig_native = compute_key.pk_sig();
                let pk_sig = <C::AccountSignatureGadget as SignatureGadget<
                    C::AccountSignatureScheme,
                    C::InnerScalarField,
                >>::PublicKeyGadget::alloc(
                    &mut account_cs.ns(|| "Declare pk_sig"), || Ok(pk_sig_native)
                )?;
                let sk_prf = C::PRFGadget::new_seed(&mut account_cs.ns(|| "Declare sk_prf"), compute_key.sk_prf());
                let r_pk = <C::AccountCommitmentGadget as CommitmentGadget<
                    C::AccountCommitmentScheme,
                    C::InnerScalarField,
                >>::RandomnessGadget::alloc(&mut account_cs.ns(|| "Declare r_pk"), || {
                    Ok(compute_key.r_pk())
                })?;

                (pk_sig, sk_prf, r_pk)
            };

            // Construct the account view key.
            let candidate_account_view_key = {
                let mut account_view_key_input = pk_sig.to_bytes(&mut account_cs.ns(|| "pk_sig to_bytes"))?;
                account_view_key_input.extend_from_slice(&sk_prf);

                // This is the record decryption key.
                let candidate_account_commitment = account_commitment_parameters.check_commitment_gadget(
                    &mut account_cs.ns(|| "Compute the account commitment."),
                    &account_view_key_input,
                    &r_pk,
                )?;

                // Enforce the account commitment bytes (padded) correspond to the
                // given account's view key bytes (padded). This is equivalent to
                // verifying that the base field element from the computed account
                // commitment contains the same bit-value as the scalar field element
                // computed from the given account private key.
                {
                    // Derive the given account view key based on the given account private key.
                    //
                    // This allocation also enforces that the private key is well-formed in our definition,
                    // i.e., the private key is within the limit of the capacity.
                    let given_account_view_key = <C::AccountEncryptionGadget as EncryptionGadget<
                        C::AccountEncryptionScheme,
                        C::InnerScalarField,
                    >>::PrivateKeyGadget::alloc(
                        &mut account_cs.ns(|| "Allocate account view key"),
                        || {
                            Ok(compute_key
                                .to_decryption_key()
                                .map_err(|_| SynthesisError::AssignmentMissing)?)
                        },
                    )?;

                    let given_account_view_key_bytes =
                        given_account_view_key.to_bytes(&mut account_cs.ns(|| "given_account_view_key to_bytes"))?;

                    let candidate_account_commitment_bytes = candidate_account_commitment
                        .to_bytes(&mut account_cs.ns(|| "candidate_account_commitment to_bytes"))?;

                    candidate_account_commitment_bytes.enforce_equal(
                        &mut account_cs.ns(|| "Check that candidate and given account view keys are equal"),
                        &given_account_view_key_bytes,
                    )?;

                    given_account_view_key
                }
            };

            // Construct and verify the record owner - account address.
            {
                let candidate_record_owner = account_encryption_parameters.check_public_key_gadget(
                    &mut account_cs.ns(|| "Compute the candidate record owner - account address"),
                    &candidate_account_view_key,
                )?;

                candidate_record_owner.enforce_equal(
                    &mut account_cs.ns(|| "Check that declared and computed addresses are equal"),
                    &given_owner,
                )?;
            }

            (sk_prf, pk_sig)
        };
        // ********************************************************************

        // ********************************************************************
        // Check that the serial number is derived correctly.
        // ********************************************************************
        {
            let sn_cs = &mut cs.ns(|| "Check that sn is derived correctly");

            let prf_seed = sk_prf;
            let randomizer = <C::PRFGadget as PRFGadget<C::PRF, C::InnerScalarField>>::check_evaluation_gadget(
                &mut sn_cs.ns(|| "Compute pk_sig randomizer"),
                &prf_seed,
                &given_serial_number_nonce_bytes,
            )?;
            let randomizer_bytes = randomizer.to_bytes(&mut sn_cs.ns(|| "Convert randomizer to bytes"))?;

            let candidate_serial_number_gadget = account_signature_parameters.randomize_public_key(
                &mut sn_cs.ns(|| "Compute serial number"),
                &pk_sig,
                &randomizer_bytes,
            )?;

            let given_serial_number_gadget = <C::AccountSignatureGadget as SignatureGadget<
                C::AccountSignatureScheme,
                C::InnerScalarField,
            >>::PublicKeyGadget::alloc_input(
                &mut sn_cs.ns(|| "Declare given serial number"),
                || Ok(given_serial_number),
            )?;

            candidate_serial_number_gadget.enforce_equal(
                &mut sn_cs.ns(|| "Check that given and computed serial numbers are equal"),
                &given_serial_number_gadget,
            )?;

            // Convert input serial numbers to bytes
            let bytes = candidate_serial_number_gadget
                .to_bytes(&mut sn_cs.ns(|| format!("Convert {}-th serial number to bytes", i)))?;
            old_serial_numbers_bytes_gadgets.extend_from_slice(&bytes);

            old_serial_numbers_gadgets.push(candidate_serial_number_gadget);
        };
        // ********************************************************************

        // *******************************************************************
        // Check that the record is well-formed.
        // *******************************************************************
        {
            let commitment_cs = &mut cs.ns(|| "Check that record is well-formed");

            // Perform noop safety checks.
            given_value.conditional_enforce_equal(
                &mut commitment_cs.ns(|| format!("If the input record {} is a noop, enforce it has a value of 0", i)),
                &zero_value,
                &given_is_dummy,
            )?;
            given_payload.conditional_enforce_equal(
                &mut commitment_cs
                    .ns(|| format!("If the input record {} is a noop, enforce it has an empty payload", i)),
                &empty_payload,
                &given_is_dummy,
            )?;

            // Compute the record commitment and check that it matches the declared commitment.
            let record_owner_bytes = given_owner.to_bytes(&mut commitment_cs.ns(|| "Convert record_owner to bytes"))?;
            let is_dummy_bytes = given_is_dummy.to_bytes(&mut commitment_cs.ns(|| "Convert is_dummy to bytes"))?;

            let mut commitment_input = Vec::new();
            commitment_input.extend_from_slice(&given_program_id);
            commitment_input.extend_from_slice(&record_owner_bytes);
            commitment_input.extend_from_slice(&is_dummy_bytes);
            commitment_input.extend_from_slice(&given_value);
            commitment_input.extend_from_slice(&given_payload);
            commitment_input.extend_from_slice(&given_serial_number_nonce_bytes);

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

    let mut new_record_commitments_gadgets = Vec::with_capacity(private.output_records.len());
    let mut new_program_ids_gadgets = Vec::with_capacity(private.output_records.len());

    for (j, (((record, commitment), encryption_randomness), encrypted_record_hash)) in private
        .output_records
        .iter()
        .zip(&public.kernel.commitments)
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

            let given_owner = <C::AccountEncryptionGadget as EncryptionGadget<
                C::AccountEncryptionScheme,
                C::InnerScalarField,
            >>::PublicKeyGadget::alloc(
                &mut declare_cs.ns(|| "given_record_owner"),
                || Ok(record.owner().to_encryption_key()),
            )?;

            let given_is_dummy = Boolean::alloc(&mut declare_cs.ns(|| "given_is_dummy"), || Ok(record.is_dummy()))?;

            let given_value = UInt8::alloc_vec(&mut declare_cs.ns(|| "given_value"), &record.value().to_bytes_le()?)?;

            let given_payload =
                UInt8::alloc_vec(&mut declare_cs.ns(|| "given_payload"), &record.payload().to_bytes_le()?)?;

            let given_serial_number_nonce = <C::SerialNumberNonceCRHGadget as CRHGadget<
                C::SerialNumberNonceCRH,
                C::InnerScalarField,
            >>::OutputGadget::alloc(
                &mut declare_cs.ns(|| "given_serial_number_nonce"),
                || Ok(record.serial_number_nonce()),
            )?;

            let given_serial_number_nonce_bytes =
                given_serial_number_nonce.to_bytes(&mut declare_cs.ns(|| "Convert sn nonce to bytes"))?;

            let given_commitment = {
                let record_commitment = <C::RecordCommitmentGadget as CommitmentGadget<
                    C::RecordCommitmentScheme,
                    C::InnerScalarField,
                >>::OutputGadget::alloc(
                    &mut declare_cs.ns(|| "record_commitment"), || Ok(record.commitment())
                )?;

                let public_commitment = <C::RecordCommitmentGadget as CommitmentGadget<
                    C::RecordCommitmentScheme,
                    C::InnerScalarField,
                >>::OutputGadget::alloc_input(
                    &mut declare_cs.ns(|| "public_commitment"), || Ok(commitment)
                )?;

                record_commitment.enforce_equal(
                    &mut declare_cs.ns(|| "Check that record commitment matches the public commitment"),
                    &public_commitment,
                )?;

                record_commitment
            };
            new_record_commitments_gadgets.push(given_commitment.clone());

            let given_commitment_randomness = <C::RecordCommitmentGadget as CommitmentGadget<
                C::RecordCommitmentScheme,
                C::InnerScalarField,
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
        // Check that the serial number nonce is computed correctly.
        // *******************************************************************
        {
            let sn_cs = &mut cs.ns(|| "Check that serial number nonce is computed correctly");

            let record_position = UInt8::constant((C::NUM_INPUT_RECORDS + j) as u8);
            let mut serial_number_nonce_input_bytes_le = vec![record_position];
            serial_number_nonce_input_bytes_le.extend_from_slice(&old_serial_numbers_bytes_gadgets);

            let candidate_serial_number_nonce = serial_number_nonce_crh.check_evaluation_gadget(
                &mut sn_cs.ns(|| "Compute serial number nonce"),
                serial_number_nonce_input_bytes_le,
            )?;

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
            given_value.conditional_enforce_equal(
                &mut commitment_cs.ns(|| format!("If the output record {} is a noop, enforce it has a value of 0", j)),
                &zero_value,
                &given_is_dummy,
            )?;
            given_payload.conditional_enforce_equal(
                &mut commitment_cs
                    .ns(|| format!("If the output record {} is a noop, enforce it has an empty payload", j)),
                &empty_payload,
                &given_is_dummy,
            )?;

            // Compute the record commitment and check that it matches the declared commitment.
            let given_owner_bytes = given_owner.to_bytes(&mut commitment_cs.ns(|| "Convert record_owner to bytes"))?;
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

            let encryption_randomness_gadget = <C::AccountEncryptionGadget as EncryptionGadget<
                C::AccountEncryptionScheme,
                C::InnerScalarField,
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

            let encrypted_record_hash_gadget = <C::EncryptedRecordCRHGadget as CRHGadget<
                C::EncryptedRecordCRH,
                C::InnerScalarField,
            >>::OutputGadget::alloc_input(
                &mut encryption_cs.ns(|| format!("output record {} encrypted record hash", j)),
                || Ok(encrypted_record_hash),
            )?;

            let candidate_encrypted_record_gadget_field_elements = candidate_encrypted_record_gadget
                .to_constraint_field(
                    &mut encryption_cs.ns(|| format!("convert encrypted record {} to field elements", j)),
                )?;

            let candidate_encrypted_record_hash = encrypted_record_crh.check_evaluation_gadget_on_field_elements(
                &mut encryption_cs.ns(|| format!("Compute encrypted record hash {}", j)),
                candidate_encrypted_record_gadget_field_elements,
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

        let mut input = Vec::new();
        for id_gadget in old_program_ids_gadgets.iter().take(C::NUM_INPUT_RECORDS) {
            input.extend_from_slice(id_gadget);
        }
        for id_gadget in new_program_ids_gadgets.iter().take(C::NUM_OUTPUT_RECORDS) {
            input.extend_from_slice(id_gadget);
        }

        let given_commitment_randomness =
            <C::ProgramCommitmentGadget as CommitmentGadget<_, C::InnerScalarField>>::RandomnessGadget::alloc(
                &mut commitment_cs.ns(|| "given_commitment_randomness"),
                || Ok(&private.program_randomness),
            )?;

        let given_commitment =
            <C::ProgramCommitmentGadget as CommitmentGadget<_, C::InnerScalarField>>::OutputGadget::alloc_input(
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
    // Check that the local data root is valid
    // ********************************************************************
    {
        let mut cs = cs.ns(|| "Check that local data root is valid.");

        let memo = UInt8::alloc_input_vec_le(cs.ns(|| "Allocate memorandum"), &public.kernel.memo)?;
        let network_id = UInt8::alloc_input_vec_le(cs.ns(|| "Allocate network id"), &[public.kernel.network_id])?;

        let mut old_record_commitment_bytes = vec![];
        for i in 0..C::NUM_INPUT_RECORDS {
            let mut cs = cs.ns(|| format!("Construct local data with input record {}", i));

            let mut input_bytes = vec![];
            input_bytes.extend_from_slice(&[UInt8::constant(i as u8)]);
            input_bytes.extend_from_slice(&old_serial_numbers_gadgets[i].to_bytes(&mut cs.ns(|| "serial_number"))?);
            input_bytes.extend_from_slice(&old_record_commitments_gadgets[i].to_bytes(&mut cs.ns(|| "commitment"))?);
            input_bytes.extend_from_slice(&memo);
            input_bytes.extend_from_slice(&network_id);

            let commitment_randomness = <C::LocalDataCommitmentGadget as CommitmentGadget<
                C::LocalDataCommitmentScheme,
                C::InnerScalarField,
            >>::RandomnessGadget::alloc(
                cs.ns(|| format!("Allocate old record local data commitment randomness {}", i)),
                || Ok(&private.local_data_leaf_randomizers[i]),
            )?;

            let commitment = local_data_commitment_parameters.check_commitment_gadget(
                cs.ns(|| format!("Commit to old record local data {}", i)),
                &input_bytes,
                &commitment_randomness,
            )?;

            old_record_commitment_bytes
                .extend_from_slice(&commitment.to_bytes(&mut cs.ns(|| "old_record_local_data"))?);
        }

        let mut new_record_commitment_bytes = Vec::new();
        for j in 0..C::NUM_OUTPUT_RECORDS {
            let mut cs = cs.ns(|| format!("Construct local data with output record {}", j));

            let mut input_bytes = vec![];
            input_bytes.extend_from_slice(&[UInt8::constant((C::NUM_INPUT_RECORDS + j) as u8)]);
            input_bytes
                .extend_from_slice(&new_record_commitments_gadgets[j].to_bytes(&mut cs.ns(|| "record_commitment"))?);
            input_bytes.extend_from_slice(&memo);
            input_bytes.extend_from_slice(&network_id);

            let commitment_randomness = <C::LocalDataCommitmentGadget as CommitmentGadget<
                C::LocalDataCommitmentScheme,
                C::InnerScalarField,
            >>::RandomnessGadget::alloc(
                cs.ns(|| format!("Allocate new record local data commitment randomness {}", j)),
                || Ok(&private.local_data_leaf_randomizers[C::NUM_INPUT_RECORDS + j]),
            )?;

            let commitment = local_data_commitment_parameters.check_commitment_gadget(
                cs.ns(|| format!("Commit to new record local data {}", j)),
                &input_bytes,
                &commitment_randomness,
            )?;

            new_record_commitment_bytes
                .extend_from_slice(&commitment.to_bytes(&mut cs.ns(|| "new_record_local_data"))?);
        }

        let inner1_commitment_hash = local_data_crh.check_evaluation_gadget(
            cs.ns(|| "Compute to local data commitment inner1 hash"),
            old_record_commitment_bytes,
        )?;

        let inner2_commitment_hash = local_data_crh.check_evaluation_gadget(
            cs.ns(|| "Compute to local data commitment inner2 hash"),
            new_record_commitment_bytes,
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
            <C::LocalDataCRHGadget as CRHGadget<C::LocalDataCRH, C::InnerScalarField>>::OutputGadget::alloc_input(
                cs.ns(|| "Allocate local data root"),
                || Ok(public.local_data_root.unwrap()),
            )?;

        candidate_local_data_root.enforce_equal(
            &mut cs.ns(|| "Check that local data root is valid"),
            &given_local_data_root,
        )?;
    }
    // *******************************************************************

    // *******************************************************************
    // Check that the value balance is valid
    // *******************************************************************
    {
        let mut cs = cs.ns(|| "Check that the value balance is valid.");

        let given_value_balance =
            Int64::alloc_input_fe(cs.ns(|| "given_value_balance"), public.kernel.value_balance.0)?;

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
    }

    Ok(())
}
