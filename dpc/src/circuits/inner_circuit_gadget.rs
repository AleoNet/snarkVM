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

use crate::{record::Record, AleoAmount, Parameters, PrivateKey, RecordScheme};
use snarkvm_algorithms::{
    merkle_tree::{MerklePath, MerkleTreeDigest},
    CommitmentScheme,
    EncryptionScheme,
    MerkleParameters,
    SignatureScheme,
};
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
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};
use snarkvm_utilities::{to_bytes_le, ToBytes};

#[allow(clippy::too_many_arguments)]
pub fn execute_inner_circuit<C: Parameters, CS: ConstraintSystem<C::InnerScalarField>>(
    cs: &mut CS,
    // Ledger
    ledger_digest: &MerkleTreeDigest<C::RecordCommitmentTreeParameters>,

    // Old record stuff
    old_records: &[Record<C>],
    old_witnesses: &[MerklePath<C::RecordCommitmentTreeParameters>],
    old_private_keys: &[PrivateKey<C>],
    old_serial_numbers: &[<C::AccountSignatureScheme as SignatureScheme>::PublicKey],

    // New record stuff
    new_records: &[Record<C>],
    new_commitments: &[C::RecordCommitment],

    new_records_encryption_randomness: &[<C::AccountEncryptionScheme as EncryptionScheme>::Randomness],
    new_encrypted_record_hashes: &[C::EncryptedRecordDigest],

    // Rest
    program_commitment: &<C::ProgramCommitmentScheme as CommitmentScheme>::Output,
    program_randomness: &<C::ProgramCommitmentScheme as CommitmentScheme>::Randomness,
    local_data_root: &C::LocalDataDigest,
    local_data_commitment_randomizers: &[<C::LocalDataCommitmentScheme as CommitmentScheme>::Randomness],
    memo: &[u8; 64],
    value_balance: AleoAmount,
    network_id: u8,
) -> Result<(), SynthesisError> {
    inner_circuit_gadget::<C, CS>(
        cs,
        ledger_digest,
        //
        old_records,
        old_witnesses,
        old_private_keys,
        old_serial_numbers,
        //
        new_records,
        new_commitments,
        new_records_encryption_randomness,
        new_encrypted_record_hashes,
        //
        program_commitment,
        program_randomness,
        local_data_root,
        local_data_commitment_randomizers,
        memo,
        value_balance,
        network_id,
    )
}

#[allow(clippy::too_many_arguments)]
fn inner_circuit_gadget<C, CS: ConstraintSystem<C::InnerScalarField>>(
    cs: &mut CS,
    ledger_digest: &MerkleTreeDigest<C::RecordCommitmentTreeParameters>,

    //
    old_records: &[Record<C>],
    old_witnesses: &[MerklePath<C::RecordCommitmentTreeParameters>],
    old_private_keys: &[PrivateKey<C>],
    old_serial_numbers: &[<C::AccountSignatureScheme as SignatureScheme>::PublicKey],

    //
    new_records: &[Record<C>],
    new_commitments: &[C::RecordCommitment],
    new_records_encryption_randomness: &[<C::AccountEncryptionScheme as EncryptionScheme>::Randomness],
    new_encrypted_record_hashes: &[C::EncryptedRecordDigest],

    //
    program_commitment: &<C::ProgramCommitmentScheme as CommitmentScheme>::Output,
    program_randomness: &<C::ProgramCommitmentScheme as CommitmentScheme>::Randomness,
    local_data_root: &C::LocalDataDigest,
    local_data_commitment_randomizers: &[<C::LocalDataCommitmentScheme as CommitmentScheme>::Randomness],
    memo: &[u8; 64],
    value_balance: AleoAmount,
    network_id: u8,
) -> Result<(), SynthesisError>
where
    C: Parameters,
{
    // Order for allocation of input:
    // 1. ledger_digest
    // 2. for i in 0..NUM_INPUT_RECORDS: old_serial_numbers[i]
    // 3. for j in 0..NUM_OUTPUT_RECORDS: new_commitments[i], new_encrypted_record_hashes[i]
    // 4. program_commitment
    // 5. local_data_root
    let (
        account_commitment_parameters,
        account_encryption_parameters,
        account_signature_parameters,
        record_commitment_parameters,
        encrypted_record_crh,
        program_id_commitment_parameters,
        local_data_crh,
        local_data_commitment_parameters,
        serial_number_nonce_crh,
        record_commitment_tree_parameters,
    ) = {
        let cs = &mut cs.ns(|| "Declare commitment and CRH parameters");

        let account_commitment_parameters =
            C::AccountCommitmentGadget::alloc_constant(&mut cs.ns(|| "Declare account commit parameters"), || {
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

        let program_id_commitment_parameters = C::ProgramCommitmentGadget::alloc_constant(
            &mut cs.ns(|| "Declare program ID commitment parameters"),
            || Ok(C::program_commitment_scheme().clone()),
        )?;

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
            program_id_commitment_parameters,
            local_data_crh_parameters,
            local_data_commitment_parameters,
            serial_number_nonce_crh_parameters,
            record_commitment_tree_parameters,
        )
    };

    let zero_value = UInt8::alloc_vec(&mut cs.ns(|| "Declare record zero value"), &to_bytes_le![0u64]?)?;

    let digest_gadget = <C::RecordCommitmentTreeCRHGadget as CRHGadget<_, _>>::OutputGadget::alloc_input(
        &mut cs.ns(|| "Declare ledger digest"),
        || Ok(ledger_digest),
    )?;

    let mut old_serial_numbers_gadgets = Vec::with_capacity(old_records.len());
    let mut old_serial_numbers_bytes_gadgets = Vec::with_capacity(old_records.len() * 32); // Serial numbers are 32 bytes
    let mut old_record_commitments_gadgets = Vec::with_capacity(old_records.len());
    let mut old_death_program_ids_gadgets = Vec::with_capacity(old_records.len());

    for (i, (((record, witness), account_private_key), given_serial_number)) in old_records
        .iter()
        .zip(old_witnesses)
        .zip(old_private_keys)
        .zip(old_serial_numbers)
        .enumerate()
    {
        let cs = &mut cs.ns(|| format!("Process input record {}", i));

        // Declare record contents
        let (
            given_record_owner,
            given_commitment,
            given_is_dummy,
            given_value,
            given_payload,
            given_birth_program_id,
            given_death_program_id,
            given_commitment_randomness,
            serial_number_nonce,
        ) = {
            let declare_cs = &mut cs.ns(|| "Declare input record");

            // No need to check that commitments, public keys and hashes are in
            // prime order subgroup because the commitment and CRH parameters
            // are trusted, and so when we recompute these, the newly computed
            // values will always be in correct subgroup. If the input cm, pk
            // or hash is incorrect, then it will not match the computed equivalent.
            let given_record_owner = <C::AccountEncryptionGadget as EncryptionGadget<
                C::AccountEncryptionScheme,
                C::InnerScalarField,
            >>::PublicKeyGadget::alloc(
                &mut declare_cs.ns(|| "given_record_owner"),
                || Ok(record.owner().to_encryption_key()),
            )?;

            let given_commitment = <C::RecordCommitmentGadget as CommitmentGadget<
                C::RecordCommitmentScheme,
                C::InnerScalarField,
            >>::OutputGadget::alloc(
                &mut declare_cs.ns(|| "given_commitment"), || Ok(record.commitment())
            )?;
            old_record_commitments_gadgets.push(given_commitment.clone());

            let given_is_dummy = Boolean::alloc(&mut declare_cs.ns(|| "given_is_dummy"), || Ok(record.is_dummy()))?;

            let given_value = UInt8::alloc_vec(&mut declare_cs.ns(|| "given_value"), &to_bytes_le![record.value()]?)?;

            let given_payload = UInt8::alloc_vec(&mut declare_cs.ns(|| "given_payload"), &record.payload().to_bytes())?;

            let given_birth_program_id = UInt8::alloc_vec(
                &mut declare_cs.ns(|| "given_birth_program_id"),
                &record.birth_program_id(),
            )?;

            let given_death_program_id = UInt8::alloc_vec(
                &mut declare_cs.ns(|| "given_death_program_id"),
                &record.death_program_id(),
            )?;
            old_death_program_ids_gadgets.push(given_death_program_id.clone());

            let given_commitment_randomness = <C::RecordCommitmentGadget as CommitmentGadget<
                C::RecordCommitmentScheme,
                C::InnerScalarField,
            >>::RandomnessGadget::alloc(
                &mut declare_cs.ns(|| "given_commitment_randomness"),
                || Ok(record.commitment_randomness()),
            )?;

            let serial_number_nonce = <C::SerialNumberNonceCRHGadget as CRHGadget<
                C::SerialNumberNonceCRH,
                C::InnerScalarField,
            >>::OutputGadget::alloc(
                &mut declare_cs.ns(|| "serial_number_nonce"),
                || Ok(record.serial_number_nonce()),
            )?;
            (
                given_record_owner,
                given_commitment,
                given_is_dummy,
                given_value,
                given_payload,
                given_birth_program_id,
                given_death_program_id,
                given_commitment_randomness,
                serial_number_nonce,
            )
        };

        // ********************************************************************
        // Check that the commitment appears on the ledger,
        // i.e., the membership witness is valid with respect to the
        // transaction set digest.
        // ********************************************************************
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
                let pk_sig_native = account_private_key
                    .pk_sig()
                    .map_err(|_| SynthesisError::AssignmentMissing)?;
                let pk_sig = <C::AccountSignatureGadget as SignatureGadget<
                    C::AccountSignatureScheme,
                    C::InnerScalarField,
                >>::PublicKeyGadget::alloc(
                    &mut account_cs.ns(|| "Declare pk_sig"), || Ok(&pk_sig_native)
                )?;
                let sk_prf =
                    C::PRFGadget::new_seed(&mut account_cs.ns(|| "Declare sk_prf"), &account_private_key.sk_prf);
                let r_pk = <C::AccountCommitmentGadget as CommitmentGadget<
                    C::AccountCommitmentScheme,
                    C::InnerScalarField,
                >>::RandomnessGadget::alloc(&mut account_cs.ns(|| "Declare r_pk"), || {
                    Ok(&account_private_key.r_pk)
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
                let given_account_view_key = {
                    // Derive the given account view key based on the given account private key.
                    let given_account_view_key = <C::AccountEncryptionGadget as EncryptionGadget<
                        C::AccountEncryptionScheme,
                        C::InnerScalarField,
                    >>::PrivateKeyGadget::alloc(
                        &mut account_cs.ns(|| "Allocate account view key"),
                        || {
                            account_private_key
                                .to_decryption_key()
                                .map_err(|_| SynthesisError::AssignmentMissing)
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
                };

                given_account_view_key
            };

            // Construct and verify the record owner - account address.
            {
                let candidate_record_owner = account_encryption_parameters.check_public_key_gadget(
                    &mut account_cs.ns(|| "Compute the candidate record owner - account address"),
                    &candidate_account_view_key,
                )?;

                candidate_record_owner.enforce_equal(
                    &mut account_cs.ns(|| "Check that declared and computed addresses are equal"),
                    &given_record_owner,
                )?;
            }

            (sk_prf, pk_sig)
        };
        // ********************************************************************

        // ********************************************************************
        // Check that the serial number is derived correctly.
        // ********************************************************************
        let serial_number_nonce_bytes = {
            let sn_cs = &mut cs.ns(|| "Check that sn is derived correctly");

            let serial_number_nonce_bytes = serial_number_nonce.to_bytes(&mut sn_cs.ns(|| "Convert nonce to bytes"))?;

            let prf_seed = sk_prf;
            let randomizer = <C::PRFGadget as PRFGadget<C::PRF, C::InnerScalarField>>::check_evaluation_gadget(
                &mut sn_cs.ns(|| "Compute pk_sig randomizer"),
                &prf_seed,
                &serial_number_nonce_bytes,
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

            serial_number_nonce_bytes
        };
        // ********************************************************************

        // *******************************************************************
        // Check that the record is well-formed.
        // *******************************************************************
        {
            let commitment_cs = &mut cs.ns(|| "Check that record is well-formed");

            given_value.conditional_enforce_equal(
                &mut commitment_cs
                    .ns(|| format!("Enforce that if old record {} is a dummy, that it has a value of 0", i)),
                &zero_value,
                &given_is_dummy,
            )?;

            let record_owner_bytes =
                given_record_owner.to_bytes(&mut commitment_cs.ns(|| "Convert record_owner to bytes"))?;
            let is_dummy_bytes = given_is_dummy.to_bytes(&mut commitment_cs.ns(|| "Convert is_dummy to bytes"))?;

            let mut commitment_input = Vec::new();
            commitment_input.extend_from_slice(&record_owner_bytes);
            commitment_input.extend_from_slice(&is_dummy_bytes);
            commitment_input.extend_from_slice(&given_value);
            commitment_input.extend_from_slice(&given_payload);
            commitment_input.extend_from_slice(&given_birth_program_id);
            commitment_input.extend_from_slice(&given_death_program_id);
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

    let mut new_record_commitments_gadgets = Vec::with_capacity(new_records.len());
    let mut new_birth_program_ids_gadgets = Vec::with_capacity(new_records.len());

    for (j, (((record, commitment), encryption_randomness), encrypted_record_hash)) in new_records
        .iter()
        .zip(new_commitments)
        .zip(new_records_encryption_randomness)
        .zip(new_encrypted_record_hashes)
        .enumerate()
    {
        let cs = &mut cs.ns(|| format!("Process output record {}", j));

        let (
            given_record_owner,
            given_record_commitment,
            given_commitment,
            given_is_dummy,
            given_value,
            given_payload,
            given_birth_program_id,
            given_death_program_id,
            given_commitment_randomness,
            serial_number_nonce,
            serial_number_nonce_bytes,
        ) = {
            let declare_cs = &mut cs.ns(|| "Declare output record");

            let given_record_owner = <C::AccountEncryptionGadget as EncryptionGadget<
                C::AccountEncryptionScheme,
                C::InnerScalarField,
            >>::PublicKeyGadget::alloc(
                &mut declare_cs.ns(|| "given_record_owner"),
                || Ok(record.owner().to_encryption_key()),
            )?;

            let given_record_commitment = <C::RecordCommitmentGadget as CommitmentGadget<
                C::RecordCommitmentScheme,
                C::InnerScalarField,
            >>::OutputGadget::alloc(
                &mut declare_cs.ns(|| "given_record_commitment"),
                || Ok(record.commitment()),
            )?;
            new_record_commitments_gadgets.push(given_record_commitment.clone());

            let given_commitment = <C::RecordCommitmentGadget as CommitmentGadget<
                C::RecordCommitmentScheme,
                C::InnerScalarField,
            >>::OutputGadget::alloc_input(
                &mut declare_cs.ns(|| "given_commitment"), || Ok(commitment)
            )?;

            let given_is_dummy = Boolean::alloc(&mut declare_cs.ns(|| "given_is_dummy"), || Ok(record.is_dummy()))?;

            let given_value = UInt8::alloc_vec(&mut declare_cs.ns(|| "given_value"), &to_bytes_le![record.value()]?)?;

            let given_payload = UInt8::alloc_vec(&mut declare_cs.ns(|| "given_payload"), &record.payload().to_bytes())?;

            let given_birth_program_id = UInt8::alloc_vec(
                &mut declare_cs.ns(|| "given_birth_program_id"),
                &record.birth_program_id(),
            )?;
            new_birth_program_ids_gadgets.push(given_birth_program_id.clone());

            let given_death_program_id = UInt8::alloc_vec(
                &mut declare_cs.ns(|| "given_death_program_id"),
                &record.death_program_id(),
            )?;

            let given_commitment_randomness = <C::RecordCommitmentGadget as CommitmentGadget<
                C::RecordCommitmentScheme,
                C::InnerScalarField,
            >>::RandomnessGadget::alloc(
                &mut declare_cs.ns(|| "given_commitment_randomness"),
                || Ok(record.commitment_randomness()),
            )?;

            let serial_number_nonce = <C::SerialNumberNonceCRHGadget as CRHGadget<
                C::SerialNumberNonceCRH,
                C::InnerScalarField,
            >>::OutputGadget::alloc(
                &mut declare_cs.ns(|| "serial_number_nonce"),
                || Ok(record.serial_number_nonce()),
            )?;

            let serial_number_nonce_bytes =
                serial_number_nonce.to_bytes(&mut declare_cs.ns(|| "Convert sn nonce to bytes"))?;

            (
                given_record_owner,
                given_record_commitment,
                given_commitment,
                given_is_dummy,
                given_value,
                given_payload,
                given_birth_program_id,
                given_death_program_id,
                given_commitment_randomness,
                serial_number_nonce,
                serial_number_nonce_bytes,
            )
        };
        // ********************************************************************

        // *******************************************************************
        // Check that the serial number nonce is computed correctly.
        // *******************************************************************
        {
            let sn_cs = &mut cs.ns(|| "Check that serial number nonce is computed correctly");

            let current_record_number = UInt8::constant((C::NUM_INPUT_RECORDS + j) as u8);
            let mut current_record_number_bytes_le = vec![current_record_number];
            current_record_number_bytes_le.extend_from_slice(&old_serial_numbers_bytes_gadgets);

            let sn_nonce_input = current_record_number_bytes_le;

            let candidate_sn_nonce = serial_number_nonce_crh
                .check_evaluation_gadget(&mut sn_cs.ns(|| "Compute serial number nonce"), sn_nonce_input)?;
            candidate_sn_nonce.enforce_equal(
                &mut sn_cs.ns(|| "Check that computed nonce matches provided nonce"),
                &serial_number_nonce,
            )?;
        }
        // *******************************************************************

        // *******************************************************************
        // Check that the record is well-formed.
        // *******************************************************************
        {
            let commitment_cs = &mut cs.ns(|| "Check that record is well-formed");

            given_value.conditional_enforce_equal(
                &mut commitment_cs
                    .ns(|| format!("Enforce that if new record {} is a dummy, that it has a value of 0", j)),
                &zero_value,
                &given_is_dummy,
            )?;

            let record_owner_bytes =
                given_record_owner.to_bytes(&mut commitment_cs.ns(|| "Convert record_owner to bytes"))?;
            let is_dummy_bytes = given_is_dummy.to_bytes(&mut commitment_cs.ns(|| "Convert is_dummy to bytes"))?;

            let mut commitment_input = Vec::new();
            commitment_input.extend_from_slice(&record_owner_bytes);
            commitment_input.extend_from_slice(&is_dummy_bytes);
            commitment_input.extend_from_slice(&given_value);
            commitment_input.extend_from_slice(&given_payload);
            commitment_input.extend_from_slice(&given_birth_program_id);
            commitment_input.extend_from_slice(&given_death_program_id);
            commitment_input.extend_from_slice(&serial_number_nonce_bytes);

            let candidate_commitment = record_commitment_parameters.check_commitment_gadget(
                &mut commitment_cs.ns(|| "Compute record commitment"),
                &commitment_input,
                &given_commitment_randomness,
            )?;
            candidate_commitment.enforce_equal(
                &mut commitment_cs.ns(|| "Check that computed commitment matches public input"),
                &given_commitment,
            )?;
            candidate_commitment.enforce_equal(
                &mut commitment_cs.ns(|| "Check that computed commitment matches declared commitment"),
                &given_record_commitment,
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
            // Convert serial number nonce, commitment_randomness, birth program id, death program id, value, and payload into bits

            let plaintext_bytes = {
                let mut res = vec![];

                // Serial number nonce
                res.extend_from_slice(&serial_number_nonce_bytes);

                // Commitment randomness
                let given_commitment_randomness_bytes = given_commitment_randomness
                    .to_bytes(&mut encryption_cs.ns(|| "Convert commitment randomness to bytes"))?;
                res.extend_from_slice(&given_commitment_randomness_bytes);

                // Birth program ID
                res.extend_from_slice(&given_birth_program_id);

                // Death program ID
                res.extend_from_slice(&given_death_program_id);

                // Value
                res.extend_from_slice(&given_value);

                // Payload
                res.extend_from_slice(&given_payload);

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
                &given_record_owner,
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
    // Check that program commitment is well formed.
    // *******************************************************************
    {
        let commitment_cs = &mut cs.ns(|| "Check that program commitment is well-formed");

        let mut input = Vec::new();
        for id_gadget in old_death_program_ids_gadgets.iter().take(C::NUM_INPUT_RECORDS) {
            input.extend_from_slice(id_gadget);
        }

        for id_gadget in new_birth_program_ids_gadgets.iter().take(C::NUM_OUTPUT_RECORDS) {
            input.extend_from_slice(id_gadget);
        }

        let given_commitment_randomness =
            <C::ProgramCommitmentGadget as CommitmentGadget<_, C::InnerScalarField>>::RandomnessGadget::alloc(
                &mut commitment_cs.ns(|| "given_commitment_randomness"),
                || Ok(program_randomness),
            )?;

        let given_commitment =
            <C::ProgramCommitmentGadget as CommitmentGadget<_, C::InnerScalarField>>::OutputGadget::alloc_input(
                &mut commitment_cs.ns(|| "given_commitment"),
                || Ok(program_commitment),
            )?;

        let candidate_commitment = program_id_commitment_parameters.check_commitment_gadget(
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

        let memo = UInt8::alloc_input_vec_le(cs.ns(|| "Allocate memorandum"), memo)?;
        let network_id = UInt8::alloc_input_vec_le(cs.ns(|| "Allocate network id"), &[network_id])?;

        let mut old_record_commitment_bytes = vec![];
        let mut input_bytes = vec![];
        for i in 0..C::NUM_INPUT_RECORDS {
            let mut cs = cs.ns(|| format!("Construct local data with input record {}", i));

            input_bytes.extend_from_slice(&old_serial_numbers_gadgets[i].to_bytes(&mut cs.ns(|| "old_serial_number"))?);
            input_bytes.extend_from_slice(
                &old_record_commitments_gadgets[i].to_bytes(&mut cs.ns(|| "old_record_commitment"))?,
            );
            input_bytes.extend_from_slice(&memo);
            input_bytes.extend_from_slice(&network_id);

            let commitment_randomness = <C::LocalDataCommitmentGadget as CommitmentGadget<
                C::LocalDataCommitmentScheme,
                C::InnerScalarField,
            >>::RandomnessGadget::alloc(
                cs.ns(|| format!("Allocate old record local data commitment randomness {}", i)),
                || Ok(&local_data_commitment_randomizers[i]),
            )?;

            let commitment = local_data_commitment_parameters.check_commitment_gadget(
                cs.ns(|| format!("Commit to old record local data {}", i)),
                &input_bytes,
                &commitment_randomness,
            )?;

            old_record_commitment_bytes
                .extend_from_slice(&commitment.to_bytes(&mut cs.ns(|| "old_record_local_data"))?);

            input_bytes.clear();
        }
        drop(input_bytes);

        let mut new_record_commitment_bytes = Vec::new();
        let mut input_bytes = vec![];
        for j in 0..C::NUM_OUTPUT_RECORDS {
            let mut cs = cs.ns(|| format!("Construct local data with output record {}", j));

            input_bytes
                .extend_from_slice(&new_record_commitments_gadgets[j].to_bytes(&mut cs.ns(|| "record_commitment"))?);
            input_bytes.extend_from_slice(&memo);
            input_bytes.extend_from_slice(&network_id);

            let commitment_randomness = <C::LocalDataCommitmentGadget as CommitmentGadget<
                C::LocalDataCommitmentScheme,
                C::InnerScalarField,
            >>::RandomnessGadget::alloc(
                cs.ns(|| format!("Allocate new record local data commitment randomness {}", j)),
                || Ok(&local_data_commitment_randomizers[C::NUM_INPUT_RECORDS + j]),
            )?;

            let commitment = local_data_commitment_parameters.check_commitment_gadget(
                cs.ns(|| format!("Commit to new record local data {}", j)),
                &input_bytes,
                &commitment_randomness,
            )?;

            new_record_commitment_bytes
                .extend_from_slice(&commitment.to_bytes(&mut cs.ns(|| "new_record_local_data"))?);

            input_bytes.clear();
        }
        drop(input_bytes);

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

        let declared_local_data_root =
            <C::LocalDataCRHGadget as CRHGadget<C::LocalDataCRH, C::InnerScalarField>>::OutputGadget::alloc_input(
                cs.ns(|| "Allocate local data root"),
                || Ok(local_data_root),
            )?;

        candidate_local_data_root.enforce_equal(
            &mut cs.ns(|| "Check that local data root is valid"),
            &declared_local_data_root,
        )?;
    }
    // *******************************************************************

    // *******************************************************************
    // Check that the value balance is valid
    // *******************************************************************
    {
        let mut cs = cs.ns(|| "Check that the value balance is valid.");

        let given_value_balance = Int64::alloc_input_fe(cs.ns(|| "given_value_balance"), value_balance.0)?;

        let mut candidate_value_balance = Int64::zero();

        for (i, old_record) in old_records.iter().enumerate() {
            let value = old_record.value as i64;
            let record_value = Int64::alloc(cs.ns(|| format!("old record {} value", i)), || Ok(value))?;

            candidate_value_balance = candidate_value_balance
                .add(cs.ns(|| format!("add old record {} value", i)), &record_value)
                .unwrap();
        }

        for (j, new_record) in new_records.iter().enumerate() {
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
