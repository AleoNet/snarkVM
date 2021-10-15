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

use crate::SignatureScheme;
use snarkvm_utilities::FromBytes;

use rand::SeedableRng;
use rand_chacha::ChaChaRng;

fn sign_and_verify<S: SignatureScheme>(message: &[u8]) {
    let rng = &mut ChaChaRng::seed_from_u64(1231275789u64);
    let signature_scheme = S::setup("sign_and_verify");

    let private_key = signature_scheme.generate_private_key(rng);
    let public_key = signature_scheme.generate_public_key(&private_key);
    let signature = signature_scheme.sign(&private_key, message, rng).unwrap();
    assert!(signature_scheme.verify(&public_key, &message, &signature).unwrap());
}

fn failed_verification<S: SignatureScheme>(message: &[u8], bad_message: &[u8]) {
    let rng = &mut ChaChaRng::seed_from_u64(1231275789u64);
    let signature_scheme = S::setup("failed_verification");

    let private_key = signature_scheme.generate_private_key(rng);
    let public_key = signature_scheme.generate_public_key(&private_key);
    let signature = signature_scheme.sign(&private_key, message, rng).unwrap();
    assert!(!signature_scheme.verify(&public_key, bad_message, &signature).unwrap());
}

fn signature_scheme_serialization<S: SignatureScheme>() {
    let signature_scheme = S::setup("signature_scheme_serialization");
    let recovered_signature_scheme: S = FromBytes::read_le(&signature_scheme.to_bytes_le().unwrap()[..]).unwrap();
    assert_eq!(signature_scheme, recovered_signature_scheme);
}

mod aleo {
    use super::*;
    use crate::signature::AleoSignatureScheme;
    use snarkvm_curves::{
        edwards_bls12::EdwardsParameters as EdwardsBls12,
        edwards_bw6::EdwardsParameters as EdwardsBW6,
    };

    #[test]
    fn test_aleo_signature_on_edwards_bls12_377() {
        type TestSignature = AleoSignatureScheme<EdwardsBls12>;

        let message = "Hi, I am an Aleo signature!";
        sign_and_verify::<TestSignature>(message.as_bytes());
        failed_verification::<TestSignature>(message.as_bytes(), b"Bad message");
    }

    #[test]
    fn test_aleo_signature_on_edwards_bw6() {
        type TestSignature = AleoSignatureScheme<EdwardsBW6>;

        let message = "Hi, I am an Aleo signature!";
        sign_and_verify::<TestSignature>(message.as_bytes());
        failed_verification::<TestSignature>(message.as_bytes(), b"Bad message");
    }

    #[test]
    fn aleo_signature_scheme_serialization() {
        signature_scheme_serialization::<AleoSignatureScheme<EdwardsBls12>>();
        signature_scheme_serialization::<AleoSignatureScheme<EdwardsBW6>>();
    }
}
