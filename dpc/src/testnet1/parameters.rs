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

use crate::testnet1::Testnet1Components;
use snarkvm_algorithms::prelude::*;

use std::io::Result as IoResult;

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Testnet1Components"))]
pub struct SystemParameters<C: Testnet1Components> {
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
    pub fn setup() -> Self {
        let time = start_timer!(|| "Encrypted record CRH setup");
        let encrypted_record_crh = C::EncryptedRecordCRH::setup("EncryptedRecordCRH");
        end_timer!(time);

        let time = start_timer!(|| "Inner circuit ID CRH setup");
        let inner_circuit_id_crh = C::InnerCircuitIDCRH::setup("InnerCircuitIDCRH");
        end_timer!(time);

        let time = start_timer!(|| "Local data commitment setup");
        let local_data_commitment = C::LocalDataCommitment::setup("LocalDataCommitment");
        end_timer!(time);

        let time = start_timer!(|| "Local data CRH setup");
        let local_data_crh = C::LocalDataCRH::setup("LocalDataCRH");
        end_timer!(time);

        let time = start_timer!(|| "Program verifying key CRH setup");
        let program_verification_key_crh = C::ProgramVerificationKeyCRH::setup("ProgramVerificationKeyCRH");
        end_timer!(time);

        let time = start_timer!(|| "Program verification key commitment setup");
        let program_verification_key_commitment =
            C::ProgramVerificationKeyCommitment::setup("ProgramVerificationKeyCommitment");
        end_timer!(time);

        let time = start_timer!(|| "Record commitment scheme setup");
        let record_commitment = C::RecordCommitment::setup("RecordCommitment");
        end_timer!(time);

        let time = start_timer!(|| "Serial nonce CRH setup");
        let serial_number_nonce = C::SerialNumberNonceCRH::setup("SerialNumberNonceCRH");
        end_timer!(time);

        Self {
            encrypted_record_crh,
            inner_circuit_id_crh,
            local_data_crh,
            local_data_commitment,
            program_verification_key_commitment,
            program_verification_key_crh,
            record_commitment,
            serial_number_nonce,
        }
    }

    /// TODO (howardwu): TEMPORARY FOR PR #251.
    pub fn load() -> IoResult<Self> {
        Ok(Self::setup())
    }
}
