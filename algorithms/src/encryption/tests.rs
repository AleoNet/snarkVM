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

mod ecies {
    use crate::{encryption::ECIESPoseidonEncryption, EncryptionScheme};
    use snarkvm_curves::edwards_bls12::EdwardsParameters;
    use snarkvm_utilities::{FromBytes, ToBytes, UniformRand};

    use rand::{thread_rng, Rng};

    pub const ITERATIONS: usize = 1000;

    type TestEncryptionScheme = ECIESPoseidonEncryption<EdwardsParameters>;

    #[test]
    fn test_encrypt_and_decrypt() {
        let rng = &mut thread_rng();
        let encryption = TestEncryptionScheme::setup("simple_encryption");

        let private_key = encryption.generate_private_key(rng);
        let public_key = encryption.generate_public_key(&private_key);
        let (_randomness, _ciphertext_randomizer, symmetric_key) = encryption.generate_asymmetric_key(&public_key, rng);

        let number_of_bytes = 320;
        let message = (0..number_of_bytes).map(|_| u8::rand(rng)).collect::<Vec<u8>>();
        let ciphertext = encryption.encrypt(&symmetric_key, &message).unwrap();
        dbg!(ciphertext.len());
        let candidate_message = encryption.decrypt(&symmetric_key, &ciphertext).unwrap();
        assert_eq!(message, candidate_message);
    }

    #[test]
    fn test_encryption_public_key_to_bytes_le() {
        let rng = &mut thread_rng();
        let encryption = TestEncryptionScheme::setup("encryption_public_key_serialization");

        for _ in 0..ITERATIONS {
            let private_key = encryption.generate_private_key(rng);
            let public_key = encryption.generate_public_key(&private_key);

            let public_key_bytes = public_key.to_bytes_le().unwrap();
            let recovered_public_key =
                <TestEncryptionScheme as EncryptionScheme>::PublicKey::read_le(&public_key_bytes[..]).unwrap();
            assert_eq!(public_key, recovered_public_key);
        }
    }

    #[test]
    fn test_encryption_symmetric_key_commitment() {
        let rng = &mut thread_rng();
        let encryption = TestEncryptionScheme::setup("encryption_symmetric_key_commitment");

        // Compute the symmetric key commitment.
        let private_key = encryption.generate_private_key(rng);
        let public_key = encryption.generate_public_key(&private_key);
        let (_randomness, ciphertext_randomizer, symmetric_key) = encryption.generate_asymmetric_key(&public_key, rng);
        let symmetric_key_commitment = encryption.generate_symmetric_key_commitment(&symmetric_key);

        {
            // Sanity check that the symmetric key matches, when derived from the private key.
            let candidate_symmetric_key = encryption
                .generate_symmetric_key(&private_key, ciphertext_randomizer)
                .unwrap();
            assert_eq!(symmetric_key, candidate_symmetric_key);
        }
        {
            // Sanity check that the symmetric key commitment is deterministic.
            let candidate_symmetric_key_commitment = encryption.generate_symmetric_key_commitment(&symmetric_key);
            assert_eq!(symmetric_key_commitment, candidate_symmetric_key_commitment);
        }

        // Ensure different symmetric keys for the same public key fail to match the symmetric key commitment.
        for _ in 0..ITERATIONS {
            let (_randomness, _ciphertext_randomizer, alternate_symmetric_key) =
                encryption.generate_asymmetric_key(&public_key, rng);
            let candidate_symmetric_key_commitment =
                encryption.generate_symmetric_key_commitment(&alternate_symmetric_key);
            assert_ne!(symmetric_key_commitment, candidate_symmetric_key_commitment);
        }

        // Ensure different private keys fail to match the symmetric key commitment.
        for _ in 0..ITERATIONS {
            let alternate_private_key = encryption.generate_private_key(rng);
            let alternate_public_key = encryption.generate_public_key(&alternate_private_key);
            let (_randomness, _ciphertext_randomizer, alternate_symmetric_key) =
                encryption.generate_asymmetric_key(&alternate_public_key, rng);
            let candidate_symmetric_key_commitment =
                encryption.generate_symmetric_key_commitment(&alternate_symmetric_key);
            assert_ne!(symmetric_key_commitment, candidate_symmetric_key_commitment);
        }
    }

    #[test]
    fn test_ciphertext_random_manipulation() {
        let rng = &mut thread_rng();
        let encryption = TestEncryptionScheme::setup("simple_encryption");

        let private_key = encryption.generate_private_key(rng);
        let public_key = encryption.generate_public_key(&private_key);
        let (_randomness, _ciphertext_randomizer, symmetric_key) = encryption.generate_asymmetric_key(&public_key, rng);

        let number_of_bytes = 320;
        let message = (0..number_of_bytes).map(|_| u8::rand(rng)).collect::<Vec<u8>>();
        let ciphertext = encryption.encrypt(&symmetric_key, &message).unwrap();
        let candidate_message = encryption.decrypt(&symmetric_key, &ciphertext).unwrap();
        assert_eq!(message, candidate_message);

        // Ensure any mutation fails to match the original message.
        for _ in 0..ITERATIONS {
            // Copy the ciphertext.
            let mut ciphertext = ciphertext.clone();

            // Mutate one byte in the first 30 bytes of the ciphertext.
            let idx = rng.gen_range(0..30);
            ciphertext[idx] = ciphertext[idx].wrapping_add(rng.gen_range(1..u8::MAX));

            // This should fail.
            let candidate_message = encryption.decrypt(&symmetric_key, &ciphertext).unwrap();
            assert_ne!(message, candidate_message);
        }
    }
}
