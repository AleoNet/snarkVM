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
    traits::{AccountScheme, DPCComponents, DPCScheme, LedgerScheme, RecordScheme, TransactionScheme},
    Account,
    AleoAmount,
    DPCError,
    Network,
};
use snarkvm_algorithms::{
    commitment_tree::CommitmentMerkleTree,
    merkle_tree::{MerklePath, MerkleTreeDigest},
    prelude::*,
};
use snarkvm_curves::traits::{Group, MontgomeryModelParameters, ProjectiveCurve, TEModelParameters};
use snarkvm_gadgets::{
    bits::Boolean,
    traits::algorithms::{CRHGadget, SNARKVerifierGadget},
};
use snarkvm_utilities::{bytes::ToBytes, has_duplicates, rand::UniformRand, to_bytes};

use itertools::Itertools;
use rand::{CryptoRng, Rng};
use std::{marker::PhantomData, sync::Arc};

pub mod inner_circuit;
pub use inner_circuit::*;

pub mod outer_circuit;
pub use outer_circuit::*;

pub mod parameters;
pub use parameters::*;

pub mod program;
pub use program::*;

pub mod record;
pub use record::*;

pub mod transaction;
pub use transaction::*;

pub mod instantiated;

#[cfg(test)]
mod tests;

///////////////////////////////////////////////////////////////////////////////

/// Trait that stores information about the testnet1 DPC scheme.
pub trait Testnet1Components: DPCComponents {
    /// Ledger digest type.
    type MerkleParameters: LoadableMerkleParameters;
    type MerkleHashGadget: CRHGadget<<Self::MerkleParameters as MerkleParameters>::H, Self::InnerScalarField>;

    /// Group and Model Parameters for record encryption
    type EncryptionGroup: Group + ProjectiveCurve;
    type EncryptionModelParameters: MontgomeryModelParameters + TEModelParameters;

    /// SNARK for non-proof-verification checks
    type InnerSNARK: SNARK<
        Circuit = InnerCircuit<Self>,
        AllocatedCircuit = InnerCircuit<Self>,
        VerifierInput = InnerCircuitVerifierInput<Self>,
    >;

    /// SNARK Verifier gadget for the inner snark
    type InnerSNARKGadget: SNARKVerifierGadget<Self::InnerSNARK, Self::OuterScalarField, Input = Vec<Boolean>>;

    /// SNARK for proof-verification checks
    type OuterSNARK: SNARK<
        Circuit = OuterCircuit<Self>,
        AllocatedCircuit = OuterCircuit<Self>,
        VerifierInput = OuterCircuitVerifierInput<Self>,
    >;

    /// SNARK for the no-op "always-accept" that does nothing with its input.
    type NoopProgramSNARK: SNARK<
        Circuit = NoopCircuit<Self>,
        AllocatedCircuit = NoopCircuit<Self>,
        VerifierInput = ProgramLocalData<Self>,
    >;

    /// SNARK Verifier gadget for the no-op "always-accept" that does nothing with its input.
    type NoopProgramSNARKGadget: SNARKVerifierGadget<
        Self::NoopProgramSNARK,
        Self::OuterScalarField,
        Input = Vec<Boolean>,
    >;
}

///////////////////////////////////////////////////////////////////////////////

pub struct DPC<C: Testnet1Components> {
    _components: PhantomData<C>,
}

impl<C: Testnet1Components> DPC<C> {
    pub fn generate_system_parameters<R: Rng + CryptoRng>(rng: &mut R) -> Result<SystemParameters<C>, DPCError> {
        let time = start_timer!(|| "Account commitment scheme setup");
        let account_commitment = C::AccountCommitment::setup(rng);
        end_timer!(time);

        let time = start_timer!(|| "Account encryption scheme setup");
        let account_encryption = <C::AccountEncryption as EncryptionScheme>::setup(rng);
        end_timer!(time);

        let time = start_timer!(|| "Account signature setup");
        let account_signature = C::AccountSignature::setup(rng)?;
        end_timer!(time);

        let time = start_timer!(|| "Encrypted record CRH setup");
        let encrypted_record_crh = C::EncryptedRecordCRH::setup(rng);
        end_timer!(time);

        let time = start_timer!(|| "Inner circuit ID CRH setup");
        let inner_circuit_id_crh = C::InnerCircuitIDCRH::setup(rng);
        end_timer!(time);

        let time = start_timer!(|| "Local data commitment setup");
        let local_data_commitment = C::LocalDataCommitment::setup(rng);
        end_timer!(time);

        let time = start_timer!(|| "Local data CRH setup");
        let local_data_crh = C::LocalDataCRH::setup(rng);
        end_timer!(time);

        let time = start_timer!(|| "Program verifying key CRH setup");
        let program_verification_key_crh = C::ProgramVerificationKeyCRH::setup(rng);
        end_timer!(time);

        let time = start_timer!(|| "Program verification key commitment setup");
        let program_verification_key_commitment = C::ProgramVerificationKeyCommitment::setup(rng);
        end_timer!(time);

        let time = start_timer!(|| "Record commitment scheme setup");
        let record_commitment = C::RecordCommitment::setup(rng);
        end_timer!(time);

        let time = start_timer!(|| "Serial nonce CRH setup");
        let serial_number_nonce = C::SerialNumberNonceCRH::setup(rng);
        end_timer!(time);

        Ok(SystemParameters {
            account_commitment,
            account_encryption,
            account_signature,
            encrypted_record_crh,
            inner_circuit_id_crh,
            local_data_crh,
            local_data_commitment,
            program_verification_key_commitment,
            program_verification_key_crh,
            record_commitment,
            serial_number_nonce,
        })
    }

    pub fn generate_noop_program_snark_parameters<R: Rng + CryptoRng>(
        system_parameters: &SystemParameters<C>,
        rng: &mut R,
    ) -> Result<NoopProgramSNARKParameters<C>, DPCError> {
        let (pk, pvk) = C::NoopProgramSNARK::setup(&NoopCircuit::blank(system_parameters), rng)?;

        Ok(NoopProgramSNARKParameters {
            proving_key: pk,
            verifying_key: pvk.into(),
        })
    }
}

impl<C: Testnet1Components, L: LedgerScheme> DPCScheme<L> for DPC<C>
where
    L: LedgerScheme<
        Commitment = <C::RecordCommitment as CommitmentScheme>::Output,
        MerkleParameters = C::MerkleParameters,
        MerklePath = MerklePath<C::MerkleParameters>,
        MerkleTreeDigest = MerkleTreeDigest<C::MerkleParameters>,
        SerialNumber = <C::AccountSignature as SignatureScheme>::PublicKey,
        Transaction = Transaction<C>,
    >,
{
    type Account = Account<C>;
    type LocalData = LocalData<C>;
    type NetworkParameters = PublicParameters<C>;
    type Payload = <Self::Record as RecordScheme>::Payload;
    type PrivateProgramInput = PrivateProgramInput;
    type Record = Record<C>;
    type SystemParameters = SystemParameters<C>;
    type Transaction = Transaction<C>;
    type TransactionKernel = TransactionKernel<C>;

    fn setup<R: Rng + CryptoRng>(
        ledger_parameters: &Arc<C::MerkleParameters>,
        rng: &mut R,
    ) -> anyhow::Result<Self::NetworkParameters> {
        let setup_time = start_timer!(|| "DPC::setup");
        let system_parameters = Self::generate_system_parameters(rng)?;

        let program_snark_setup_time = start_timer!(|| "Dummy program SNARK setup");
        let noop_program_snark_parameters = Self::generate_noop_program_snark_parameters(&system_parameters, rng)?;
        let program_snark_proof = C::NoopProgramSNARK::prove(
            &noop_program_snark_parameters.proving_key,
            &NoopCircuit::blank(&system_parameters),
            rng,
        )?;
        end_timer!(program_snark_setup_time);

        let program_snark_vk_and_proof = PrivateProgramInput {
            verifying_key: to_bytes![noop_program_snark_parameters.verifying_key]?,
            proof: to_bytes![program_snark_proof]?,
        };

        let snark_setup_time = start_timer!(|| "Execute inner SNARK setup");
        let inner_circuit = InnerCircuit::blank(&system_parameters, ledger_parameters);
        let inner_snark_parameters = C::InnerSNARK::setup(&inner_circuit, rng)?;
        end_timer!(snark_setup_time);

        let snark_setup_time = start_timer!(|| "Execute outer SNARK setup");
        let inner_snark_vk: <C::InnerSNARK as SNARK>::VerifyingKey = inner_snark_parameters.1.clone().into();
        let inner_snark_proof = C::InnerSNARK::prove(&inner_snark_parameters.0, &inner_circuit, rng)?;

        let outer_snark_parameters = C::OuterSNARK::setup(
            &OuterCircuit::blank(
                system_parameters.clone(),
                ledger_parameters.clone(),
                inner_snark_vk,
                inner_snark_proof,
                program_snark_vk_and_proof,
            ),
            rng,
        )?;
        end_timer!(snark_setup_time);
        end_timer!(setup_time);

        let inner_snark_parameters = (Some(inner_snark_parameters.0), inner_snark_parameters.1);
        let outer_snark_parameters = (Some(outer_snark_parameters.0), outer_snark_parameters.1);

        Ok(PublicParameters {
            system_parameters,
            noop_program_snark_parameters,
            inner_snark_parameters,
            outer_snark_parameters,
        })
    }

    fn create_account<R: Rng + CryptoRng>(
        parameters: &Self::SystemParameters,
        rng: &mut R,
    ) -> anyhow::Result<Self::Account> {
        let time = start_timer!(|| "DPC::create_account");
        let account = Account::new(
            &parameters.account_signature,
            &parameters.account_commitment,
            &parameters.account_encryption,
            rng,
        )?;
        end_timer!(time);
        Ok(account)
    }

    fn execute_offline_phase<R: Rng + CryptoRng>(
        parameters: Self::SystemParameters,
        old_private_keys: &Vec<<Self::Account as AccountScheme>::PrivateKey>,
        old_records: Vec<Self::Record>,
        new_records: Vec<Self::Record>,
        memorandum: <Self::Transaction as TransactionScheme>::Memorandum,
        rng: &mut R,
    ) -> anyhow::Result<Self::TransactionKernel> {
        assert_eq!(C::NUM_INPUT_RECORDS, old_private_keys.len());
        assert_eq!(C::NUM_INPUT_RECORDS, old_records.len());
        assert_eq!(C::NUM_OUTPUT_RECORDS, new_records.len());

        let mut old_serial_numbers = Vec::with_capacity(C::NUM_INPUT_RECORDS);
        let mut old_randomizers = Vec::with_capacity(C::NUM_INPUT_RECORDS);
        let mut joint_serial_numbers = Vec::new();
        let mut old_death_program_ids = Vec::with_capacity(C::NUM_INPUT_RECORDS);

        let mut value_balance = AleoAmount::ZERO;

        // Compute the ledger membership witness and serial number from the old records.
        for (i, record) in old_records.iter().enumerate().take(C::NUM_INPUT_RECORDS) {
            let input_record_time = start_timer!(|| format!("Process input record {}", i));

            if !record.is_dummy() {
                value_balance = value_balance.add(AleoAmount::from_bytes(record.value() as i64));
            }

            let (sn, randomizer) = record.to_serial_number(&parameters.account_signature, &old_private_keys[i])?;
            joint_serial_numbers.extend_from_slice(&to_bytes![sn]?);
            old_serial_numbers.push(sn);
            old_randomizers.push(randomizer);
            old_death_program_ids.push(record.death_program_id().to_vec());

            end_timer!(input_record_time);
        }

        let mut new_birth_program_ids = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);
        let mut new_commitments = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);
        let mut new_sn_nonce_randomness = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);

        for (j, record) in new_records.iter().enumerate().take(C::NUM_OUTPUT_RECORDS) {
            let output_record_time = start_timer!(|| format!("Process output record {}", j));

            new_birth_program_ids.push(record.birth_program_id());
            new_commitments.push(record.commitment());
            new_sn_nonce_randomness.push(match record.serial_number_nonce_randomness() {
                Some(randomness) => randomness.clone(),
                None => {
                    return Err(DPCError::Message(format!(
                        "New record {} is missing its serial number nonce randomness",
                        j
                    ))
                    .into());
                }
            });

            if !record.is_dummy() {
                value_balance = value_balance.sub(AleoAmount::from_bytes(record.value() as i64));
            }

            end_timer!(output_record_time);
        }

        // TODO (raychu86) Add index and program register inputs + outputs to local data commitment leaves
        let local_data_merkle_tree_timer = start_timer!(|| "Compute local data merkle tree");

        let mut local_data_commitment_randomizers = Vec::with_capacity(C::NUM_INPUT_RECORDS);

        let mut old_record_commitments = Vec::with_capacity(C::NUM_INPUT_RECORDS);
        for i in 0..C::NUM_INPUT_RECORDS {
            let record = &old_records[i];
            let input_bytes = to_bytes![old_serial_numbers[i], record.commitment(), memorandum, C::NETWORK_ID]?;

            let commitment_randomness = <C::LocalDataCommitment as CommitmentScheme>::Randomness::rand(rng);
            let commitment = C::LocalDataCommitment::commit(
                &parameters.local_data_commitment,
                &input_bytes,
                &commitment_randomness,
            )?;

            old_record_commitments.push(commitment);
            local_data_commitment_randomizers.push(commitment_randomness);
        }

        let mut new_record_commitments = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);
        for record in new_records.iter().take(C::NUM_OUTPUT_RECORDS) {
            let input_bytes = to_bytes![record.commitment(), memorandum, C::NETWORK_ID]?;

            let commitment_randomness = <C::LocalDataCommitment as CommitmentScheme>::Randomness::rand(rng);
            let commitment = C::LocalDataCommitment::commit(
                &parameters.local_data_commitment,
                &input_bytes,
                &commitment_randomness,
            )?;

            new_record_commitments.push(commitment);
            local_data_commitment_randomizers.push(commitment_randomness);
        }

        let leaves = [
            old_record_commitments[0].clone(),
            old_record_commitments[1].clone(),
            new_record_commitments[0].clone(),
            new_record_commitments[1].clone(),
        ];
        let local_data_merkle_tree = CommitmentMerkleTree::new(parameters.local_data_crh.clone(), &leaves)?;

        end_timer!(local_data_merkle_tree_timer);

        let program_comm_timer = start_timer!(|| "Compute program commitment");
        let (program_commitment, program_randomness) = {
            let mut input = Vec::new();
            for id in old_death_program_ids {
                input.extend_from_slice(&id);
            }

            for id in new_birth_program_ids {
                input.extend_from_slice(&id);
            }
            let program_randomness = <C::ProgramVerificationKeyCommitment as CommitmentScheme>::Randomness::rand(rng);
            let program_commitment = C::ProgramVerificationKeyCommitment::commit(
                &parameters.program_verification_key_commitment,
                &input,
                &program_randomness,
            )?;
            (program_commitment, program_randomness)
        };
        end_timer!(program_comm_timer);

        // Encrypt the new records

        let mut new_records_encryption_randomness = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);
        let mut new_encrypted_records = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);

        for record in &new_records {
            let (encrypted_record, record_encryption_randomness) = EncryptedRecord::encrypt(&parameters, record, rng)?;

            new_records_encryption_randomness.push(record_encryption_randomness);
            new_encrypted_records.push(encrypted_record);
        }

        // Construct the ciphertext hashes
        let mut new_encrypted_record_hashes = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);
        for encrypted_record in &new_encrypted_records {
            new_encrypted_record_hashes.push(encrypted_record.to_hash(&parameters)?);
        }

        Ok(TransactionKernel {
            system_parameters: parameters,

            old_records,
            old_serial_numbers,
            old_randomizers,

            new_records,
            new_sn_nonce_randomness,
            new_commitments,

            new_records_encryption_randomness,
            new_encrypted_records,
            new_encrypted_record_hashes,

            program_commitment,
            program_randomness,
            local_data_merkle_tree,
            local_data_commitment_randomizers,

            value_balance,
            memorandum,
            network_id: C::NETWORK_ID,
        })
    }

    fn execute_online_phase<R: Rng + CryptoRng>(
        parameters: &Self::NetworkParameters,
        old_private_keys: &Vec<<Self::Account as AccountScheme>::PrivateKey>,
        transaction_kernel: Self::TransactionKernel,
        program_proofs: Vec<Self::PrivateProgramInput>,
        ledger: &L,
        rng: &mut R,
    ) -> anyhow::Result<(Vec<Self::Record>, Self::Transaction)> {
        assert_eq!(C::NUM_INPUT_RECORDS, old_private_keys.len());
        assert_eq!(C::NUM_TOTAL_RECORDS, program_proofs.len());

        let exec_time = start_timer!(|| "DPC::execute_online_phase");

        let TransactionKernel {
            system_parameters,

            old_records,
            old_serial_numbers,
            old_randomizers,

            new_records,
            new_sn_nonce_randomness,
            new_commitments,

            new_records_encryption_randomness,
            new_encrypted_records,
            new_encrypted_record_hashes,

            program_commitment,
            program_randomness,
            local_data_merkle_tree,
            local_data_commitment_randomizers,
            value_balance,
            memorandum,
            network_id,
        } = transaction_kernel;

        let local_data_root = local_data_merkle_tree.root();

        // Construct the ledger witnesses

        let ledger_digest = ledger.digest().expect("could not get digest");

        // Generate the ledger membership witnesses
        let mut old_witnesses = Vec::with_capacity(C::NUM_INPUT_RECORDS);

        // Compute the ledger membership witness and serial number from the old records.
        for record in old_records.iter() {
            if record.is_dummy() {
                old_witnesses.push(MerklePath::default());
            } else {
                let witness = ledger.prove_cm(&record.commitment())?;
                old_witnesses.push(witness);
            }
        }

        // Generate Schnorr signature on transaction data
        // TODO (raychu86) Remove ledger_digest from signature and move the schnorr signing into `execute_offline_phase`
        let signature_time = start_timer!(|| "Sign and randomize transaction contents");

        let signature_message = to_bytes![
            network_id,
            ledger_digest,
            old_serial_numbers,
            new_commitments,
            program_commitment,
            local_data_root,
            value_balance,
            memorandum
        ]?;

        let mut signatures = Vec::with_capacity(C::NUM_INPUT_RECORDS);
        for i in 0..C::NUM_INPUT_RECORDS {
            let sk_sig = &old_private_keys[i].sk_sig;
            let randomizer = &old_randomizers[i];

            // Sign the transaction data
            let account_signature =
                C::AccountSignature::sign(&system_parameters.account_signature, sk_sig, &signature_message, rng)?;

            // Randomize the signature
            let randomized_signature = C::AccountSignature::randomize_signature(
                &system_parameters.account_signature,
                &account_signature,
                randomizer,
            )?;

            signatures.push(randomized_signature);
        }

        end_timer!(signature_time);

        // Prepare record encryption components used in the inner SNARK

        let mut new_records_encryption_gadget_components = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);

        for (record, ciphertext_randomness) in new_records.iter().zip_eq(&new_records_encryption_randomness) {
            let record_encryption_gadget_components = EncryptedRecord::prepare_encryption_gadget_components(
                &system_parameters,
                &record,
                ciphertext_randomness,
            )?;

            new_records_encryption_gadget_components.push(record_encryption_gadget_components);
        }

        let inner_proof = {
            let circuit = InnerCircuit::new(
                parameters.system_parameters.clone(),
                ledger.parameters().clone(),
                ledger_digest.clone(),
                old_records,
                old_witnesses,
                old_private_keys.clone(),
                old_serial_numbers.clone(),
                new_records.clone(),
                new_sn_nonce_randomness,
                new_commitments.clone(),
                new_records_encryption_randomness,
                new_records_encryption_gadget_components,
                new_encrypted_record_hashes.clone(),
                program_commitment.clone(),
                program_randomness.clone(),
                local_data_root.clone(),
                local_data_commitment_randomizers,
                memorandum,
                value_balance,
                network_id,
            );

            let inner_snark_parameters = match &parameters.inner_snark_parameters.0 {
                Some(inner_snark_parameters) => inner_snark_parameters,
                None => return Err(DPCError::MissingInnerSnarkProvingParameters.into()),
            };

            C::InnerSNARK::prove(&inner_snark_parameters, &circuit, rng)?
        };

        // Verify that the inner proof passes
        {
            let input = InnerCircuitVerifierInput {
                system_parameters: parameters.system_parameters.clone(),
                ledger_parameters: ledger.parameters().clone(),
                ledger_digest: ledger_digest.clone(),
                old_serial_numbers: old_serial_numbers.clone(),
                new_commitments: new_commitments.clone(),
                new_encrypted_record_hashes: new_encrypted_record_hashes.clone(),
                memo: memorandum,
                program_commitment: program_commitment.clone(),
                local_data_root: local_data_root.clone(),
                value_balance,
                network_id,
            };

            assert!(C::InnerSNARK::verify(
                &parameters.inner_snark_parameters.1,
                &input,
                &inner_proof
            )?);
        }

        let inner_snark_vk: <C::InnerSNARK as SNARK>::VerifyingKey = parameters.inner_snark_parameters.1.clone().into();

        let inner_circuit_id =
            <C::InnerCircuitIDCRH as CRH>::hash(&parameters.system_parameters.inner_circuit_id_crh, &to_bytes![
                inner_snark_vk
            ]?)?;

        let transaction_proof = {
            let circuit = OuterCircuit::new(
                parameters.system_parameters.clone(),
                ledger.parameters().clone(),
                ledger_digest.clone(),
                old_serial_numbers.clone(),
                new_commitments.clone(),
                new_encrypted_record_hashes,
                memorandum,
                value_balance,
                network_id,
                inner_snark_vk,
                inner_proof,
                program_proofs,
                program_commitment.clone(),
                program_randomness,
                local_data_root.clone(),
                inner_circuit_id.clone(),
            );

            let outer_snark_parameters = match &parameters.outer_snark_parameters.0 {
                Some(outer_snark_parameters) => outer_snark_parameters,
                None => return Err(DPCError::MissingOuterSnarkProvingParameters.into()),
            };

            C::OuterSNARK::prove(&outer_snark_parameters, &circuit, rng)?
        };

        let transaction = Self::Transaction::new(
            old_serial_numbers,
            new_commitments,
            memorandum,
            ledger_digest,
            inner_circuit_id,
            transaction_proof,
            program_commitment,
            local_data_root,
            value_balance,
            Network::from_id(network_id),
            signatures,
            new_encrypted_records,
        );

        end_timer!(exec_time);

        Ok((new_records, transaction))
    }

    fn verify(parameters: &Self::NetworkParameters, transaction: &Self::Transaction, ledger: &L) -> bool {
        let verify_time = start_timer!(|| "DPC::verify");

        // Returns false if the number of serial numbers in the transaction is incorrect.
        if transaction.old_serial_numbers().len() != C::NUM_INPUT_RECORDS {
            eprintln!("Transaction contains incorrect number of serial numbers");
            return false;
        }

        // Returns false if there are duplicate serial numbers in the transaction.
        if has_duplicates(transaction.old_serial_numbers().iter()) {
            eprintln!("Transaction contains duplicate serial numbers");
            return false;
        }

        // Returns false if the number of commitments in the transaction is incorrect.
        if transaction.new_commitments().len() != C::NUM_OUTPUT_RECORDS {
            eprintln!("Transaction contains incorrect number of commitments");
            return false;
        }

        // Returns false if there are duplicate commitments numbers in the transaction.
        if has_duplicates(transaction.new_commitments().iter()) {
            eprintln!("Transaction contains duplicate commitments");
            return false;
        }

        let ledger_time = start_timer!(|| "Ledger checks");

        // Returns false if the transaction memo previously existed in the ledger.
        if ledger.contains_memo(transaction.memorandum()) {
            eprintln!("Ledger already contains this transaction memo.");
            return false;
        }

        // Returns false if any transaction serial number previously existed in the ledger.
        for sn in transaction.old_serial_numbers() {
            if ledger.contains_sn(sn) {
                eprintln!("Ledger already contains this transaction serial number.");
                return false;
            }
        }

        // Returns false if any transaction commitment previously existed in the ledger.
        for cm in transaction.new_commitments() {
            if ledger.contains_cm(cm) {
                eprintln!("Ledger already contains this transaction commitment.");
                return false;
            }
        }

        // Returns false if the ledger digest in the transaction is invalid.
        if !ledger.validate_digest(&transaction.ledger_digest) {
            eprintln!("Ledger digest is invalid.");
            return false;
        }

        end_timer!(ledger_time);

        let signature_time = start_timer!(|| "Signature checks");

        // Returns false if the number of signatures in the transaction is incorrect.
        if transaction.signatures().len() != C::NUM_OUTPUT_RECORDS {
            eprintln!("Transaction contains incorrect number of commitments");
            return false;
        }

        let signature_message = match to_bytes![
            transaction.network_id(),
            transaction.ledger_digest(),
            transaction.old_serial_numbers(),
            transaction.new_commitments(),
            transaction.program_commitment(),
            transaction.local_data_root(),
            transaction.value_balance(),
            transaction.memorandum()
        ] {
            Ok(message) => message,
            _ => {
                eprintln!("Unable to construct signature message.");
                return false;
            }
        };

        let account_signature = &parameters.system_parameters.account_signature;
        for (pk, sig) in transaction.old_serial_numbers().iter().zip(transaction.signatures()) {
            match C::AccountSignature::verify(account_signature, pk, &signature_message, sig) {
                Ok(is_valid) => {
                    if !is_valid {
                        eprintln!("Signature failed to verify.");
                        return false;
                    }
                }
                _ => {
                    eprintln!("Unable to verify signature.");
                    return false;
                }
            }
        }

        end_timer!(signature_time);

        // Construct the ciphertext hashes

        // Returns false if the number of encrypted records in the transaction is incorrect.
        if transaction.encrypted_records().len() != C::NUM_OUTPUT_RECORDS {
            eprintln!("Transaction contains incorrect number of encrypted records");
            return false;
        }

        let mut new_encrypted_record_hashes = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);
        for encrypted_record in transaction.encrypted_records() {
            match encrypted_record.to_hash(&parameters.system_parameters) {
                Ok(hash) => new_encrypted_record_hashes.push(hash),
                _ => {
                    eprintln!("Unable to hash encrypted record.");
                    return false;
                }
            }
        }

        let inner_snark_input = InnerCircuitVerifierInput {
            system_parameters: parameters.system_parameters.clone(),
            ledger_parameters: ledger.parameters().clone(),
            ledger_digest: transaction.ledger_digest().clone(),
            old_serial_numbers: transaction.old_serial_numbers().to_vec(),
            new_commitments: transaction.new_commitments().to_vec(),
            new_encrypted_record_hashes,
            memo: *transaction.memorandum(),
            program_commitment: transaction.program_commitment().clone(),
            local_data_root: transaction.local_data_root().clone(),
            value_balance: transaction.value_balance(),
            network_id: transaction.network_id(),
        };

        let inner_snark_vk: <<C as Testnet1Components>::InnerSNARK as SNARK>::VerifyingKey =
            parameters.inner_snark_parameters.1.clone().into();

        let inner_snark_vk_bytes = match to_bytes![inner_snark_vk] {
            Ok(bytes) => bytes,
            _ => {
                eprintln!("Unable to convert inner snark vk into bytes.");
                return false;
            }
        };

        let outer_snark_input = OuterCircuitVerifierInput {
            inner_snark_verifier_input: inner_snark_input,
            inner_circuit_id: match C::InnerCircuitIDCRH::hash(
                &parameters.system_parameters.inner_circuit_id_crh,
                &inner_snark_vk_bytes,
            ) {
                Ok(hash) => hash,
                _ => {
                    eprintln!("Unable to hash inner snark vk.");
                    return false;
                }
            },
        };

        match C::OuterSNARK::verify(
            &parameters.outer_snark_parameters.1,
            &outer_snark_input,
            &transaction.transaction_proof,
        ) {
            Ok(is_valid) => {
                if !is_valid {
                    eprintln!("Transaction proof failed to verify.");
                    return false;
                }
            }
            _ => {
                eprintln!("Unable to verify transaction proof.");
                return false;
            }
        }

        end_timer!(verify_time);

        true
    }

    /// Returns true iff all the transactions in the block are valid according to the ledger.
    fn verify_transactions(
        parameters: &Self::NetworkParameters,
        transactions: &[Self::Transaction],
        ledger: &L,
    ) -> bool {
        for transaction in transactions {
            if !Self::verify(parameters, transaction, ledger) {
                return false;
            }
        }

        true
    }
}
