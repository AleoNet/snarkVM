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

use super::{encoded::*, encrypted::*};
use crate::{
    testnet1::{instantiated::*, NoopProgramSNARKParameters, Payload, Record, SystemParameters},
    traits::{AccountScheme, DPCComponents, EncodedRecordScheme},
    Account,
    ViewKey,
};
use snarkvm_algorithms::traits::CRH;
use snarkvm_curves::edwards_bls12::{EdwardsParameters, EdwardsProjective as EdwardsBls};
use snarkvm_utilities::{bytes::ToBytes, to_bytes};

use rand::{Rng, SeedableRng};
use rand_chacha::ChaChaRng;

pub(crate) const ITERATIONS: usize = 5;

#[test]
fn test_record_encoding() {
    let mut rng = ChaChaRng::seed_from_u64(1231275789u64);

    for _ in 0..ITERATIONS {
        // Generate parameters for the ledger, commitment schemes, CRH, and the
        // "always-accept" program.
        let system_parameters = SystemParameters::<Components>::setup(&mut rng).unwrap();
        let noop_program_snark_pp = NoopProgramSNARKParameters::setup(&system_parameters, &mut rng).unwrap();

        let program_snark_vk_bytes = to_bytes![
            <Components as DPCComponents>::ProgramVerificationKeyCRH::hash(
                &system_parameters.program_verification_key_crh,
                &to_bytes![noop_program_snark_pp.verifying_key].unwrap()
            )
            .unwrap()
        ]
        .unwrap();

        for _ in 0..ITERATIONS {
            let dummy_account = Account::<Components>::new(
                &system_parameters.account_signature,
                &system_parameters.account_commitment,
                &system_parameters.account_encryption,
                &mut rng,
            )
            .unwrap();

            let sn_nonce_input: [u8; 32] = rng.gen();
            let value = rng.gen();
            let payload: [u8; 32] = rng.gen();

            let given_record = Record::new(
                &system_parameters.record_commitment,
                dummy_account.address,
                false,
                value,
                Payload::from_bytes(&payload),
                program_snark_vk_bytes.clone(),
                program_snark_vk_bytes.clone(),
                <Components as DPCComponents>::SerialNumberNonceCRH::hash(
                    &system_parameters.serial_number_nonce,
                    &sn_nonce_input,
                )
                .unwrap(),
                &mut rng,
            )
            .unwrap();

            let encoded_record = EncodedRecord::<_, EdwardsParameters, EdwardsBls>::encode(&given_record).unwrap();
            let record_components = encoded_record.decode().unwrap();

            assert_eq!(given_record.serial_number_nonce, record_components.serial_number_nonce);
            assert_eq!(
                given_record.commitment_randomness,
                record_components.commitment_randomness
            );
            assert_eq!(given_record.birth_program_id, record_components.birth_program_id);
            assert_eq!(given_record.death_program_id, record_components.death_program_id);
            assert_eq!(given_record.value, record_components.value);
            assert_eq!(given_record.payload, record_components.payload);
        }
    }
}

#[test]
fn test_record_encryption() {
    let mut rng = ChaChaRng::seed_from_u64(1231275789u64);

    for _ in 0..ITERATIONS {
        // Generate parameters for the ledger, commitment schemes, CRH, and the
        // "always-accept" program.
        let system_parameters = SystemParameters::<Components>::setup(&mut rng).unwrap();
        let program_snark_pp = NoopProgramSNARKParameters::setup(&system_parameters, &mut rng).unwrap();

        let program_snark_vk_bytes = to_bytes![
            <Components as DPCComponents>::ProgramVerificationKeyCRH::hash(
                &system_parameters.program_verification_key_crh,
                &to_bytes![program_snark_pp.verifying_key].unwrap()
            )
            .unwrap()
        ]
        .unwrap();

        for _ in 0..ITERATIONS {
            let dummy_account = Account::new(
                &system_parameters.account_signature,
                &system_parameters.account_commitment,
                &system_parameters.account_encryption,
                &mut rng,
            )
            .unwrap();

            let sn_nonce_input: [u8; 32] = rng.gen();
            let value = rng.gen();
            let payload: [u8; 32] = rng.gen();

            let given_record = Record::new(
                &system_parameters.record_commitment,
                dummy_account.address,
                false,
                value,
                Payload::from_bytes(&payload),
                program_snark_vk_bytes.clone(),
                program_snark_vk_bytes.clone(),
                <Components as DPCComponents>::SerialNumberNonceCRH::hash(
                    &system_parameters.serial_number_nonce,
                    &sn_nonce_input,
                )
                .unwrap(),
                &mut rng,
            )
            .unwrap();

            // Encrypt the record
            let (encryped_record, _) = EncryptedRecord::encrypt(&system_parameters, &given_record, &mut rng).unwrap();
            let account_view_key = ViewKey::from_private_key(
                &system_parameters.account_signature,
                &system_parameters.account_commitment,
                &dummy_account.private_key,
            )
            .unwrap();

            // Decrypt the record
            let decrypted_record = encryped_record.decrypt(&system_parameters, &account_view_key).unwrap();

            assert_eq!(given_record, decrypted_record);
        }
    }
}
