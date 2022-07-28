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

#[macro_use]
extern crate criterion;

use snarkvm_dpc::{prelude::*, testnet2::Testnet2};

use criterion::Criterion;
use rand::{thread_rng, Rng};
use snarkvm_utilities::Uniform;

fn bench_record_decryption(
    c: &mut Criterion,
    benchmark_id: &str,
    decryption_key: DecryptionKey<Testnet2>,
    ciphertext: <Testnet2 as Network>::RecordCiphertext,
) {
    c.bench_function(benchmark_id, move |b| b.iter(|| Record::decrypt(&decryption_key, &ciphertext)));
}

fn record_decrypt_noop(c: &mut Criterion) {
    let rng = &mut thread_rng();
    let private_key: PrivateKey<Testnet2> = PrivateKey::new(rng);
    let address = private_key.to_address();
    let decryption_key = DecryptionKey::from(ViewKey::from_private_key(&private_key));

    let ciphertext_noop = Record::new_noop(address, rng).unwrap().ciphertext().clone();
    bench_record_decryption(c, "record_decrypt_noop", decryption_key, ciphertext_noop);
}

fn record_decrypt_with_payload(c: &mut Criterion) {
    let rng = &mut thread_rng();
    let private_key: PrivateKey<Testnet2> = PrivateKey::new(rng);
    let address = private_key.to_address();
    let decryption_key = DecryptionKey::from(ViewKey::from_private_key(&private_key));
    let mut payload = [0u8; Testnet2::RECORD_PAYLOAD_SIZE_IN_BYTES];
    rng.fill(&mut payload);

    let ciphertext_with_payload =
        Record::new(address, AleoAmount::from_gate(1234), Some(Payload::from(&payload)), None, rng)
            .unwrap()
            .ciphertext()
            .clone();
    bench_record_decryption(c, "record_decrypt_with_payload", decryption_key, ciphertext_with_payload);
}

fn record_decrypt_with_program_id(c: &mut Criterion) {
    let mut rng = &mut thread_rng();
    let private_key: PrivateKey<Testnet2> = PrivateKey::new(rng);
    let address = private_key.to_address();
    let decryption_key = DecryptionKey::from(ViewKey::from_private_key(&private_key));
    let program_id = <Testnet2 as Network>::ProgramID::rand(&mut rng);

    let ciphertext_with_program_id =
        Record::new(address, AleoAmount::from_gate(1234), None, Some(program_id), rng).unwrap().ciphertext().clone();
    bench_record_decryption(c, "record_decrypt_with_program_id", decryption_key, ciphertext_with_program_id);
}

fn record_decrypt_with_payload_and_program_id(c: &mut Criterion) {
    let mut rng = &mut thread_rng();
    let private_key: PrivateKey<Testnet2> = PrivateKey::new(rng);
    let address = private_key.to_address();
    let decryption_key = DecryptionKey::from(ViewKey::from_private_key(&private_key));

    let mut payload = [0u8; Testnet2::RECORD_PAYLOAD_SIZE_IN_BYTES];
    rng.fill(&mut payload);
    let program_id = <Testnet2 as Network>::ProgramID::rand(&mut rng);

    let ciphertext_with_program_id_and_payload =
        Record::new(address, AleoAmount::from_gate(1234), Some(Payload::from(&payload)), Some(program_id), rng)
            .unwrap()
            .ciphertext()
            .clone();
    bench_record_decryption(
        c,
        "record_decrypt_payload_and_program_id",
        decryption_key,
        ciphertext_with_program_id_and_payload,
    );
}

fn record_decrypt_with_incorrect_view_key(c: &mut Criterion) {
    let rng = &mut thread_rng();
    let private_key: PrivateKey<Testnet2> = PrivateKey::new(rng);
    let decryption_key = DecryptionKey::from(ViewKey::from_private_key(&private_key));
    let other_address: Address<Testnet2> = PrivateKey::new(rng).into();

    let ciphertext_incorrect_view_key = Record::new_noop(other_address, rng).unwrap().ciphertext().clone();
    bench_record_decryption(c, "record_decrypt_incorrect_view_key", decryption_key, ciphertext_incorrect_view_key);
}

criterion_group! {
    name = record;
    config = Criterion::default().sample_size(100);
    targets = record_decrypt_noop, record_decrypt_with_payload, record_decrypt_with_program_id, record_decrypt_with_payload_and_program_id, record_decrypt_with_incorrect_view_key
}

criterion_main!(record);
