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

mod ecies_poseidon {
    use crate::{algorithms::encryption::ECIESPoseidonEncryptionGadget, AllocGadget, EncryptionGadget, EqGadget};
    use rand::{CryptoRng, Rng, SeedableRng};
    use rand_chacha::ChaChaRng;
    use snarkvm_algorithms::{
        encoding::FieldEncodingScheme,
        encryption::ECIESPoseidonEncryption,
        EncodingScheme,
        EncryptionScheme,
    };
    use snarkvm_curves::{bls12_377::Fr, edwards_bls12::EdwardsParameters};
    use snarkvm_r1cs::{ConstraintSystem, TestConstraintSystem};
    use snarkvm_utilities::UniformRand;

    type TestEncryptionScheme = ECIESPoseidonEncryption<EdwardsParameters>;
    type TestEncryptionSchemeGadget = ECIESPoseidonEncryptionGadget<EdwardsParameters, Fr>;
    type TestEncodingScheme = FieldEncodingScheme<Fr>;

    fn generate_input<R: Rng + CryptoRng>(input_size: usize, rng: &mut R) -> Vec<u8> {
        let mut input = vec![];
        for _ in 0..input_size {
            input.push(u8::rand(rng))
        }

        input
    }

    #[test]
    fn test_ecies_poseidon_encryption_public_key_gadget() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let rng = &mut ChaChaRng::seed_from_u64(1231275789u64);

        let encryption_scheme = TestEncryptionScheme::setup("test_group_encryption_public_key_gadget");

        let private_key = encryption_scheme.generate_private_key(rng);
        let public_key = encryption_scheme.generate_public_key(&private_key).unwrap();

        let encryption =
            TestEncryptionSchemeGadget::alloc_constant(&mut cs.ns(|| "parameters_gadget"), || Ok(&encryption_scheme))
                .unwrap();
        let private_key_gadget =
            <TestEncryptionSchemeGadget as EncryptionGadget<TestEncryptionScheme, _>>::PrivateKeyGadget::alloc(
                &mut cs.ns(|| "private_key_gadget"),
                || Ok(&private_key),
            )
            .unwrap();
        let expected_public_key_gadget =
            <TestEncryptionSchemeGadget as EncryptionGadget<TestEncryptionScheme, _>>::PublicKeyGadget::alloc(
                &mut cs.ns(|| "public_key_gadget"),
                || Ok(&public_key),
            )
            .unwrap();

        println!("number of constraints for inputs: {}", cs.num_constraints());

        let public_key_gadget = encryption
            .check_public_key_gadget(&mut cs.ns(|| "public_key_gadget_evaluation"), &private_key_gadget)
            .unwrap();

        expected_public_key_gadget
            .enforce_equal(
                cs.ns(|| "Check that declared and computed public keys are equal"),
                &public_key_gadget,
            )
            .unwrap();

        println!("number of constraints total: {}", cs.num_constraints());

        if !cs.is_satisfied() {
            println!("which is unsatisfied: {:?}", cs.which_is_unsatisfied().unwrap());
        }
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_ecies_poseidon_encryption_gadget() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let rng = &mut ChaChaRng::seed_from_u64(1231275789u64);

        let encryption_scheme = TestEncryptionScheme::setup("test_encryption_gadget");
        let encoding_scheme = TestEncodingScheme::setup("test_encoding_gadget");

        let private_key = encryption_scheme.generate_private_key(rng);
        let public_key = encryption_scheme.generate_public_key(&private_key).unwrap();

        let randomness = encryption_scheme.generate_randomness(&public_key, rng).unwrap();
        let message = generate_input(10, rng);
        let plaintext = encoding_scheme.encode(&message).unwrap();
        let ciphertext = encryption_scheme.encrypt(&public_key, &randomness, &plaintext).unwrap();

        // Alloc parameters, public key, plaintext, randomness, and blinding exponents
        let encryption =
            TestEncryptionSchemeGadget::alloc_constant(&mut cs.ns(|| "parameters_gadget"), || Ok(&encryption_scheme))
                .unwrap();
        let public_key_gadget =
            <TestEncryptionSchemeGadget as EncryptionGadget<TestEncryptionScheme, _>>::PublicKeyGadget::alloc(
                &mut cs.ns(|| "public_key_gadget"),
                || Ok(&public_key),
            )
            .unwrap();
        let plaintext_gadget =
            <TestEncryptionSchemeGadget as EncryptionGadget<TestEncryptionScheme, _>>::PlaintextGadget::alloc(
                &mut cs.ns(|| "plaintext_gadget"),
                || Ok(&plaintext),
            )
            .unwrap();
        let randomness_gadget =
            <TestEncryptionSchemeGadget as EncryptionGadget<TestEncryptionScheme, _>>::RandomnessGadget::alloc(
                &mut cs.ns(|| "randomness_gadget"),
                || Ok(&randomness),
            )
            .unwrap();

        // Expected ciphertext gadget
        let expected_ciphertext_gadget =
            <TestEncryptionSchemeGadget as EncryptionGadget<TestEncryptionScheme, _>>::CiphertextGadget::alloc(
                &mut cs.ns(|| "ciphertext_gadget"),
                || Ok(&ciphertext),
            )
            .unwrap();

        println!("number of constraints for inputs: {}", cs.num_constraints());

        let ciphertext_gadget = encryption
            .check_encryption_gadget(
                &mut cs.ns(|| "ciphertext_gadget_evaluation"),
                &randomness_gadget,
                &public_key_gadget,
                &plaintext_gadget,
            )
            .unwrap();

        expected_ciphertext_gadget
            .enforce_equal(
                cs.ns(|| "Check that declared and computed ciphertexts are equal"),
                &ciphertext_gadget,
            )
            .unwrap();

        println!("number of constraints total: {}", cs.num_constraints());

        if !cs.is_satisfied() {
            println!("which is unsatisfied: {:?}", cs.which_is_unsatisfied().unwrap());
        }
        assert!(cs.is_satisfied());
    }
}
