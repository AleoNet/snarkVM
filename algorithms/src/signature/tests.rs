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

use crate::{signature::Schnorr, SignatureScheme};
use snarkvm_curves::{edwards_bls12::EdwardsProjective, edwards_bw6::EdwardsProjective as Edwards, Group};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes, UniformRand};

use rand::SeedableRng;
use rand_chacha::ChaChaRng;

type TestSignature = Schnorr<Edwards>;

fn sign_and_verify<S: SignatureScheme>(message: &[u8]) {
    let rng = &mut ChaChaRng::seed_from_u64(1231275789u64);
    let schnorr = S::setup::<_>(rng).unwrap();

    let private_key = schnorr.generate_private_key(rng).unwrap();
    let public_key = schnorr.generate_public_key(&private_key).unwrap();
    let signature = schnorr.sign(&private_key, message, rng).unwrap();
    assert!(schnorr.verify(&public_key, &message, &signature).unwrap());
}

fn failed_verification<S: SignatureScheme>(message: &[u8], bad_message: &[u8]) {
    let rng = &mut ChaChaRng::seed_from_u64(1231275789u64);
    let schnorr = S::setup::<_>(rng).unwrap();

    let private_key = schnorr.generate_private_key(rng).unwrap();
    let public_key = schnorr.generate_public_key(&private_key).unwrap();
    let signature = schnorr.sign(&private_key, message, rng).unwrap();
    assert!(!schnorr.verify(&public_key, bad_message, &signature).unwrap());
}

fn randomize_and_verify<S: SignatureScheme<Randomizer = F>, F: PrimeField>(message: &[u8], randomizer: F) {
    let rng = &mut ChaChaRng::seed_from_u64(1231275789u64);
    let schnorr = S::setup::<_>(rng).unwrap();

    let private_key = schnorr.generate_private_key(rng).unwrap();
    let public_key = schnorr.generate_public_key(&private_key).unwrap();
    let signature = schnorr.sign(&private_key, message, rng).unwrap();
    assert!(schnorr.verify(&public_key, message, &signature).unwrap());

    let randomized_private_key = schnorr.randomize_private_key(&private_key, &randomizer).unwrap();
    let randomized_public_key = schnorr.randomize_public_key(&public_key, &randomizer).unwrap();
    assert_eq!(
        randomized_public_key,
        schnorr
            .generate_public_key(&randomized_private_key.clone().into())
            .unwrap()
    );

    let randomized_signature = schnorr.sign_randomized(&randomized_private_key, message, rng).unwrap();
    assert!(signature != randomized_signature);
    assert!(
        schnorr
            .verify(&randomized_public_key, &message, &randomized_signature)
            .unwrap()
    );
}

fn signature_scheme_parameter_serialization<S: SignatureScheme>() {
    let rng = &mut ChaChaRng::seed_from_u64(1231275789u64);
    let signature_scheme = S::setup(rng).unwrap();

    let signature_scheme_parameters = signature_scheme.parameters();
    let signature_scheme_parameters_bytes = to_bytes_le![signature_scheme_parameters].unwrap();
    let recovered_signature_scheme_parameters: <S as SignatureScheme>::Parameters =
        FromBytes::read_le(&signature_scheme_parameters_bytes[..]).unwrap();

    assert_eq!(signature_scheme_parameters, &recovered_signature_scheme_parameters);
}

#[test]
fn schnorr_signature_test() {
    let message = "Hi, I am a Schnorr signature!";
    sign_and_verify::<TestSignature>(message.as_bytes());
    failed_verification::<TestSignature>(message.as_bytes(), b"Bad message");

    let rng = &mut ChaChaRng::seed_from_u64(1231275789u64);
    let randomizer = <Edwards as Group>::ScalarField::rand(rng);
    randomize_and_verify::<TestSignature, <Edwards as Group>::ScalarField>(message.as_bytes(), randomizer);
}

#[test]
fn schnorr_signature_scheme_parameters_serialization() {
    signature_scheme_parameter_serialization::<TestSignature>();
}
