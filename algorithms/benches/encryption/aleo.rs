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

#[macro_use]
extern crate criterion;

use snarkvm_algorithms::encryption::ecies_poseidon::*;
use snarkvm_algorithms::traits::EncryptionScheme as _;
use snarkvm_curves::edwards_bls12::EdwardsParameters;

use criterion::Criterion;
use rand::{self, thread_rng};

type EncryptionScheme = ECIESPoseidonEncryption<EdwardsParameters>;

fn aleo_encryption_setup(c: &mut Criterion) {
    c.bench_function("Aleo Encryption Setup", move |b| {
        b.iter(|| EncryptionScheme::setup("aleo_encryption_setup"))
    });
}

fn aleo_encryption_generate_private_key(c: &mut Criterion) {
    let rng = &mut thread_rng();
    let parameters = EncryptionScheme::setup("aleo_encryption_generate_private_key");

    c.bench_function("Aleo Encryption Generate Private Key", move |b| {
        b.iter(|| parameters.generate_private_key(rng))
    });
}

fn aleo_encryption_generate_public_key(c: &mut Criterion) {
    let rng = &mut thread_rng();
    let parameters = EncryptionScheme::setup("aleo_encryption_generate_public_key");
    let private_key = parameters.generate_private_key(rng);

    c.bench_function("Aleo Encryption Generate Public Key", move |b| {
        b.iter(|| parameters.generate_public_key(&private_key))
    });
}

fn aleo_encryption_generate_asymmetric_key(c: &mut Criterion) {
    let rng = &mut thread_rng();
    let parameters = EncryptionScheme::setup("aleo_encryption_generate_asymmetric_key");
    let private_key = parameters.generate_private_key(rng);
    let public_key = parameters.generate_public_key(&private_key);

    c.bench_function("Aleo Encryption Generate Asymmetric Key", move |b| {
        b.iter(|| parameters.generate_asymmetric_key(&public_key, rng))
    });
}

fn aleo_encryption_generate_symmetric_key(c: &mut Criterion) {
    let rng = &mut thread_rng();
    let parameters = EncryptionScheme::setup("aleo_encryption_generate_symmetric_key");
    let private_key = parameters.generate_private_key(rng);
    let public_key = parameters.generate_public_key(&private_key);
    let (_, ciphertext_randomizer, _) = parameters.generate_asymmetric_key(&public_key, rng);

    c.bench_function("Aleo Encryption Generate symmetric Key", move |b| {
        b.iter(|| parameters.generate_symmetric_key(&private_key, ciphertext_randomizer))
    });
}

fn aleo_encryption_generate_key_commitment(c: &mut Criterion) {
    let rng = &mut thread_rng();
    let parameters = EncryptionScheme::setup("aleo_encryption_generate_key_commitment");
    let private_key = parameters.generate_private_key(rng);
    let public_key = parameters.generate_public_key(&private_key);
    let (_, _, sym_key) = parameters.generate_asymmetric_key(&public_key, rng);

    c.bench_function("Aleo Encryption Generate Key Commitment", move |b| {
        b.iter(|| parameters.generate_key_commitment(&public_key, &sym_key))
    });
}

fn aleo_encryption_encrypt(c: &mut Criterion) {
    let rng = &mut thread_rng();
    let parameters = EncryptionScheme::setup("aleo_encryption_encrypt");
    let private_key = parameters.generate_private_key(rng);
    let public_key = parameters.generate_public_key(&private_key);
    let (_, _, sym_key) = parameters.generate_asymmetric_key(&public_key, rng);

    let msg = b"aleo_encryption_encrypt_encrypt_encrypt_encrypt_encrypt_encrypt";
    c.bench_function("Aleo Encryption Encrypt", move |b| {
        b.iter(|| parameters.encrypt(&sym_key, msg))
    });
}

fn aleo_encryption_decrypt(c: &mut Criterion) {
    let rng = &mut thread_rng();
    let parameters = EncryptionScheme::setup("aleo_encryption_decrypt");
    let private_key = parameters.generate_private_key(rng);
    let public_key = parameters.generate_public_key(&private_key);
    let (_, _, sym_key) = parameters.generate_asymmetric_key(&public_key, rng);
    let msg = b"aleo_encryption_encrypt_encrypt_encrypt_encrypt_encrypt_encrypt";
    let ct = parameters.encrypt(&sym_key, msg).unwrap();
    c.bench_function("Aleo Encryption Decrypt", move |b| {
        b.iter(|| parameters.decrypt(&sym_key, &ct))
    });
}

criterion_group! {
    name = aleo_encryption;
    config = Criterion::default().sample_size(20);
    targets = aleo_encryption_setup,
                aleo_encryption_generate_private_key,
                aleo_encryption_generate_public_key,
                aleo_encryption_generate_asymmetric_key,
                aleo_encryption_generate_symmetric_key,
                aleo_encryption_generate_public_key_commitment,
                aleo_encryption_encrypt,
                aleo_encryption_decrypt,
}
criterion_main!(aleo_encryption);
