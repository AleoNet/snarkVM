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

use snarkvm_algorithms::{signature::AleoSignatureScheme, SignatureScheme as SS};
use snarkvm_curves::edwards_bls12::EdwardsParameters;
use snarkvm_utilities::{test_rng, Uniform};

use criterion::Criterion;
use rand::{self, thread_rng};

type SignatureScheme = AleoSignatureScheme<EdwardsParameters>;

fn aleo_signature_setup(c: &mut Criterion) {
    c.bench_function("Aleo Signature Setup", move |b| b.iter(|| SignatureScheme::setup("aleo_signature_setup")));
}

fn aleo_signature_generate_private_key(c: &mut Criterion) {
    let rng = &mut thread_rng();
    let parameters = SignatureScheme::setup("aleo_signature_generate_private_key");

    c.bench_function("Aleo Signature Generate Private Key", move |b| {
        b.iter(|| SignatureScheme::generate_private_key(&parameters, rng))
    });
}

fn aleo_signature_generate_public_key(c: &mut Criterion) {
    let rng = &mut thread_rng();
    let parameters = SignatureScheme::setup("aleo_signature_generate_public_key");
    let private_key = SignatureScheme::generate_private_key(&parameters, rng);

    c.bench_function("Aleo Signature Generate Public Key", move |b| {
        b.iter(|| SignatureScheme::generate_public_key(&parameters, &private_key))
    });
}

fn aleo_signature_sign(c: &mut Criterion) {
    let rng = &mut thread_rng();
    let parameters = SignatureScheme::setup("aleo_signature_sign");
    let private_key = SignatureScheme::generate_private_key(&parameters, rng);
    let message = (0..128).map(|_| bool::rand(&mut test_rng())).collect::<Vec<bool>>();

    c.bench_function("Aleo Signature Sign", move |b| {
        b.iter(|| SignatureScheme::sign(&parameters, &private_key, &message, rng).unwrap())
    });
}

fn aleo_signature_verify(c: &mut Criterion) {
    let rng = &mut thread_rng();
    let parameters = SignatureScheme::setup("aleo_signature_verify");
    let private_key = SignatureScheme::generate_private_key(&parameters, rng);
    let public_key = SignatureScheme::generate_public_key(&parameters, &private_key);
    let message = (0..128).map(|_| bool::rand(&mut test_rng())).collect::<Vec<bool>>();
    let signature = SignatureScheme::sign(&parameters, &private_key, &message, rng).unwrap();

    c.bench_function("Aleo Signature Verify", move |b| {
        b.iter(|| SignatureScheme::verify(&parameters, &public_key, &message, &signature).unwrap())
    });
}

criterion_group! {
    name = aleo_signature;
    config = Criterion::default().sample_size(20);
    targets = aleo_signature_setup,
                aleo_signature_generate_private_key,
                aleo_signature_generate_public_key,
                aleo_signature_sign,
                aleo_signature_verify,
}
criterion_main!(aleo_signature);
