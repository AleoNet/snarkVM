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

use crate::{testnet1::Testnet1Components, DPCError};
use snarkvm_algorithms::prelude::*;
use snarkvm_parameters::{prelude::*, testnet1::*};
use snarkvm_utilities::bytes::FromBytes;

use rand::{CryptoRng, Rng};
use std::io::Result as IoResult;

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Testnet1Components"))]
pub struct SystemParameters<C: Testnet1Components> {
    pub account_commitment: C::AccountCommitment,
    pub account_encryption: C::AccountEncryption,
    pub account_signature: C::AccountSignature,
    pub record_commitment: C::RecordCommitment,
    pub encrypted_record_crh: C::EncryptedRecordCRH,
    pub inner_circuit_id_crh: C::InnerCircuitIDCRH,
    pub program_verification_key_commitment: C::ProgramVerificationKeyCommitment,
    pub program_verification_key_crh: C::ProgramVerificationKeyCRH,
    pub local_data_crh: C::LocalDataCRH,
    pub local_data_commitment: C::LocalDataCommitment,
    pub serial_number_nonce: C::SerialNumberNonceCRH,
}

impl<C: Testnet1Components> SystemParameters<C> {
    pub fn setup<R: Rng + CryptoRng>(rng: &mut R) -> Result<SystemParameters<C>, DPCError> {
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

        Ok(Self {
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

    /// TODO (howardwu): Inspect what is going on with program_verification_key_commitment.
    pub fn load() -> IoResult<Self> {
        let account_commitment: C::AccountCommitment =
            From::from(FromBytes::read(AccountCommitmentParameters::load_bytes()?.as_slice())?);
        let account_encryption_parameters: <C::AccountEncryption as EncryptionScheme>::Parameters =
            FromBytes::read(AccountEncryptionParameters::load_bytes()?.as_slice())?;
        let account_encryption: C::AccountEncryption = From::from(account_encryption_parameters);
        let account_signature: C::AccountSignature =
            From::from(FromBytes::read(AccountSignatureParameters::load_bytes()?.as_slice())?);
        let encrypted_record_crh: C::EncryptedRecordCRH =
            From::from(FromBytes::read(EncryptedRecordCRHParameters::load_bytes()?.as_slice())?);
        let inner_circuit_id_crh: C::InnerCircuitIDCRH =
            From::from(FromBytes::read(InnerCircuitIDCRH::load_bytes()?.as_slice())?);
        let local_data_crh: C::LocalDataCRH =
            From::from(FromBytes::read(LocalDataCRHParameters::load_bytes()?.as_slice())?);
        let local_data_commitment: C::LocalDataCommitment = From::from(FromBytes::read(
            LocalDataCommitmentParameters::load_bytes()?.as_slice(),
        )?);
        let program_verification_key_commitment: C::ProgramVerificationKeyCommitment =
            From::from(FromBytes::read(&[][..])?);
        let program_verification_key_crh: C::ProgramVerificationKeyCRH =
            From::from(FromBytes::read(ProgramVKCRHParameters::load_bytes()?.as_slice())?);
        let record_commitment: C::RecordCommitment =
            From::from(FromBytes::read(RecordCommitmentParameters::load_bytes()?.as_slice())?);
        let serial_number_nonce: C::SerialNumberNonceCRH = From::from(FromBytes::read(
            SerialNumberNonceCRHParameters::load_bytes()?.as_slice(),
        )?);

        Ok(Self {
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
}

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Testnet1Components"))]
pub struct NoopProgramSNARKParameters<C: Testnet1Components> {
    pub proving_key: <C::NoopProgramSNARK as SNARK>::ProvingKey,
    pub verifying_key: <C::NoopProgramSNARK as SNARK>::VerifyingKey,
}

impl<C: Testnet1Components> NoopProgramSNARKParameters<C> {
    // TODO (howardwu): Why are we not preparing the VK here?
    pub fn load() -> IoResult<Self> {
        let proving_key: <C::NoopProgramSNARK as SNARK>::ProvingKey =
            FromBytes::read(NoopProgramSNARKPKParameters::load_bytes()?.as_slice())?;
        let verifying_key =
            <C::NoopProgramSNARK as SNARK>::VerifyingKey::read(NoopProgramSNARKVKParameters::load_bytes()?.as_slice())?;

        Ok(Self {
            proving_key,
            verifying_key,
        })
    }
}

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Testnet1Components"))]
pub struct PublicParameters<C: Testnet1Components> {
    pub system_parameters: SystemParameters<C>,
    pub noop_program_snark_parameters: NoopProgramSNARKParameters<C>,
    pub inner_snark_parameters: (
        Option<<C::InnerSNARK as SNARK>::ProvingKey>,
        <C::InnerSNARK as SNARK>::PreparedVerifyingKey,
    ),
    pub outer_snark_parameters: (
        Option<<C::OuterSNARK as SNARK>::ProvingKey>,
        <C::OuterSNARK as SNARK>::PreparedVerifyingKey,
    ),
}

impl<C: Testnet1Components> PublicParameters<C> {
    pub fn account_commitment_parameters(&self) -> &C::AccountCommitment {
        &self.system_parameters.account_commitment
    }

    pub fn account_encryption_parameters(&self) -> &C::AccountEncryption {
        &self.system_parameters.account_encryption
    }

    pub fn account_signature_parameters(&self) -> &C::AccountSignature {
        &self.system_parameters.account_signature
    }

    pub fn inner_snark_parameters(
        &self,
    ) -> &(
        Option<<C::InnerSNARK as SNARK>::ProvingKey>,
        <C::InnerSNARK as SNARK>::PreparedVerifyingKey,
    ) {
        &self.inner_snark_parameters
    }

    pub fn local_data_crh_parameters(&self) -> &C::LocalDataCRH {
        &self.system_parameters.local_data_crh
    }

    pub fn local_data_commitment_parameters(&self) -> &C::LocalDataCommitment {
        &self.system_parameters.local_data_commitment
    }

    pub fn outer_snark_parameters(
        &self,
    ) -> &(
        Option<<C::OuterSNARK as SNARK>::ProvingKey>,
        <C::OuterSNARK as SNARK>::PreparedVerifyingKey,
    ) {
        &self.outer_snark_parameters
    }

    pub fn noop_program_snark_parameters(&self) -> &NoopProgramSNARKParameters<C> {
        &self.noop_program_snark_parameters
    }

    pub fn program_verification_key_commitment_parameters(&self) -> &C::ProgramVerificationKeyCommitment {
        &self.system_parameters.program_verification_key_commitment
    }

    pub fn program_verification_key_crh_parameters(&self) -> &C::ProgramVerificationKeyCRH {
        &self.system_parameters.program_verification_key_crh
    }

    pub fn record_commitment_parameters(&self) -> &C::RecordCommitment {
        &self.system_parameters.record_commitment
    }

    pub fn encrypted_record_crh_parameters(&self) -> &C::EncryptedRecordCRH {
        &self.system_parameters.encrypted_record_crh
    }

    pub fn serial_number_nonce_parameters(&self) -> &C::SerialNumberNonceCRH {
        &self.system_parameters.serial_number_nonce
    }

    pub fn load(verify_only: bool) -> IoResult<Self> {
        let system_parameters = SystemParameters::<C>::load()?;
        let noop_program_snark_parameters = NoopProgramSNARKParameters::<C>::load()?;

        let inner_snark_parameters = {
            let inner_snark_pk = match verify_only {
                true => None,
                false => Some(<C::InnerSNARK as SNARK>::ProvingKey::read(
                    InnerSNARKPKParameters::load_bytes()?.as_slice(),
                )?),
            };

            let inner_snark_vk: <C::InnerSNARK as SNARK>::VerifyingKey =
                <C::InnerSNARK as SNARK>::VerifyingKey::read(InnerSNARKVKParameters::load_bytes()?.as_slice())?;

            (inner_snark_pk, inner_snark_vk.into())
        };

        let outer_snark_parameters = {
            let outer_snark_pk = match verify_only {
                true => None,
                false => Some(<C::OuterSNARK as SNARK>::ProvingKey::read(
                    OuterSNARKPKParameters::load_bytes()?.as_slice(),
                )?),
            };

            let outer_snark_vk: <C::OuterSNARK as SNARK>::VerifyingKey =
                <C::OuterSNARK as SNARK>::VerifyingKey::read(OuterSNARKVKParameters::load_bytes()?.as_slice())?;

            (outer_snark_pk, outer_snark_vk.into())
        };

        Ok(Self {
            system_parameters,
            noop_program_snark_parameters,
            inner_snark_parameters,
            outer_snark_parameters,
        })
    }
}
