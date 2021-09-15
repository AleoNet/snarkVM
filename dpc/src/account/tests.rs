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

#[cfg(test)]
mod testnet1 {
    use crate::{testnet1::Testnet1Parameters, Account, AccountScheme, Address, Parameters, PrivateKey, ViewKey};
    use snarkvm_algorithms::prelude::*;
    use snarkvm_curves::AffineCurve;
    use snarkvm_utilities::ToBytes;

    use rand::{thread_rng, Rng, SeedableRng};
    use rand_chacha::ChaChaRng;
    use std::{
        convert::{TryFrom, TryInto},
        str::FromStr,
    };

    const ALEO_TESTNET1_PRIVATE_KEY: &str = "APrivateKey1zkp8cC4jgHEBnbtu3xxs1Ndja2EMizcvTRDq5Nikdkukg1p";
    const ALEO_TESTNET1_VIEW_KEY: &str = "AViewKey1mdu8XYL4v8qRkGV2zJAfC4o5mg3qFm71QLPKUqmAnthn";
    const ALEO_TESTNET1_ADDRESS: &str = "aleo13vl8qpz93jal77p7vc0ku87a44x3kul7vffrplgkn2rvtx7kts8sykhp79";

    const ITERATIONS: usize = 1000;

    #[test]
    fn test_account_new() {
        let mut rng = ChaChaRng::seed_from_u64(1231275789u64);

        // Check the seeded derivation matches the hardcoded value, as a sanity check.
        let account = Account::<Testnet1Parameters>::new(&mut rng).unwrap();
        assert_eq!(ALEO_TESTNET1_PRIVATE_KEY, account.private_key().to_string());
        assert_eq!(ALEO_TESTNET1_VIEW_KEY, account.view_key.to_string());
        assert_eq!(ALEO_TESTNET1_ADDRESS, account.address.to_string());

        // Attempt to sample for a new account ITERATIONS times.
        for _ in 0..ITERATIONS {
            assert!(Account::<Testnet1Parameters>::new(&mut rng).is_ok());
        }
    }

    #[test]
    fn test_from_private_key() {
        let private_key = PrivateKey::<Testnet1Parameters>::from_str(ALEO_TESTNET1_PRIVATE_KEY).unwrap();
        let account = Account::<Testnet1Parameters>::try_from(private_key).unwrap();

        assert_eq!(ALEO_TESTNET1_PRIVATE_KEY, account.private_key().to_string());
        assert_eq!(ALEO_TESTNET1_VIEW_KEY, account.view_key.to_string());
        assert_eq!(ALEO_TESTNET1_ADDRESS, account.address.to_string());
    }

    #[test]
    fn test_account_derivation() {
        let private_key = PrivateKey::<Testnet1Parameters>::from_str(ALEO_TESTNET1_PRIVATE_KEY).unwrap();
        let view_key = ViewKey::<Testnet1Parameters>::from_private_key(&private_key).unwrap();
        let address = Address::<Testnet1Parameters>::from_private_key(&private_key).unwrap();

        assert_eq!(ALEO_TESTNET1_PRIVATE_KEY, private_key.to_string());
        assert_eq!(ALEO_TESTNET1_VIEW_KEY, view_key.to_string());
        assert_eq!(ALEO_TESTNET1_ADDRESS, address.to_string());
    }

    #[test]
    fn test_private_key_from_str() {
        let private_key = PrivateKey::<Testnet1Parameters>::from_str(ALEO_TESTNET1_PRIVATE_KEY).unwrap();
        assert_eq!(ALEO_TESTNET1_PRIVATE_KEY, private_key.to_string());
    }

    #[test]
    fn test_private_key_from_invalid_str() {
        assert!(PrivateKey::<Testnet1Parameters>::from_str(ALEO_TESTNET1_VIEW_KEY).is_err());
        assert!(PrivateKey::<Testnet1Parameters>::from_str(ALEO_TESTNET1_ADDRESS).is_err());
        assert!(PrivateKey::<Testnet1Parameters>::from_str("APrivateKey1abcdefghijklmnopqrstuvwxyz").is_err());
        assert!(PrivateKey::<Testnet1Parameters>::from_str("APrivateKey1").is_err());
        assert!(PrivateKey::<Testnet1Parameters>::from_str("").is_err());
    }

    #[test]
    fn test_private_key_into_view_key() {
        let private_key = PrivateKey::<Testnet1Parameters>::from_str(ALEO_TESTNET1_PRIVATE_KEY).unwrap();
        let view_key: ViewKey<_> = private_key.try_into().unwrap();
        assert_eq!(ALEO_TESTNET1_VIEW_KEY, view_key.to_string());
    }

    #[test]
    fn test_view_key_from_str() {
        let view_key = ViewKey::<Testnet1Parameters>::from_str(ALEO_TESTNET1_VIEW_KEY).unwrap();
        assert_eq!(ALEO_TESTNET1_VIEW_KEY, view_key.to_string());
    }

    #[test]
    fn test_view_key_from_invalid_str() {
        assert!(ViewKey::<Testnet1Parameters>::from_str(ALEO_TESTNET1_PRIVATE_KEY).is_err());
        assert!(ViewKey::<Testnet1Parameters>::from_str(ALEO_TESTNET1_ADDRESS).is_err());
        assert!(ViewKey::<Testnet1Parameters>::from_str("AViewKey1abcdefghijklmnopqrstuvwxyz").is_err());
        assert!(ViewKey::<Testnet1Parameters>::from_str("AViewKey1").is_err());
        assert!(ViewKey::<Testnet1Parameters>::from_str("").is_err());
    }

    #[test]
    fn test_private_key_into_address() {
        let private_key = PrivateKey::<Testnet1Parameters>::from_str(ALEO_TESTNET1_PRIVATE_KEY).unwrap();
        let address: Address<_> = private_key.try_into().unwrap();
        assert_eq!(ALEO_TESTNET1_ADDRESS, address.to_string());
    }

    #[test]
    fn test_compute_key_into_address() {
        let private_key = PrivateKey::<Testnet1Parameters>::from_str(ALEO_TESTNET1_PRIVATE_KEY).unwrap();
        let compute_key = private_key.to_compute_key().unwrap();
        let address: Address<_> = compute_key.try_into().unwrap();
        assert_eq!(ALEO_TESTNET1_ADDRESS, address.to_string());
    }

    #[test]
    fn test_view_key_into_address() {
        let view_key = ViewKey::<Testnet1Parameters>::from_str(ALEO_TESTNET1_VIEW_KEY).unwrap();
        let address: Address<_> = view_key.try_into().unwrap();
        assert_eq!(ALEO_TESTNET1_ADDRESS, address.to_string());
    }

    #[test]
    fn test_address_from_str() {
        let address = Address::<Testnet1Parameters>::from_str(ALEO_TESTNET1_ADDRESS).unwrap();
        assert_eq!(ALEO_TESTNET1_ADDRESS, address.to_string());
    }

    #[test]
    fn test_address_from_invalid_str() {
        assert!(Address::<Testnet1Parameters>::from_str(ALEO_TESTNET1_PRIVATE_KEY).is_err());
        assert!(Address::<Testnet1Parameters>::from_str(ALEO_TESTNET1_VIEW_KEY).is_err());
        assert!(Address::<Testnet1Parameters>::from_str("aleo1").is_err());
        assert!(Address::<Testnet1Parameters>::from_str("").is_err());
    }

    #[test]
    fn test_account_signatures() {
        let private_key = PrivateKey::<Testnet1Parameters>::from_str(ALEO_TESTNET1_PRIVATE_KEY).unwrap();
        let address = Address::<Testnet1Parameters>::from_private_key(&private_key).unwrap();

        for i in 0..ITERATIONS {
            let message: Vec<u8> = (0..(32 * i)).map(|_| rand::random::<u8>()).collect();
            let signature = private_key.sign(&message, &mut thread_rng()).unwrap();
            let verification = address.verify_signature(&message, &signature).unwrap();
            assert!(verification);
        }
    }

    #[test]
    fn test_invalid_account_signatures() {
        let private_key = PrivateKey::<Testnet1Parameters>::from_str(ALEO_TESTNET1_PRIVATE_KEY).unwrap();
        let address = Address::<Testnet1Parameters>::from_private_key(&private_key).unwrap();

        for i in 0..ITERATIONS {
            let message = "Hi, I'm an Aleo account signature!".as_bytes();
            let incorrect_message: Vec<u8> = (0..(32 * i)).map(|_| rand::random::<u8>()).collect();

            let signature = private_key.sign(&message, &mut thread_rng()).unwrap();
            let verification = address.verify_signature(&incorrect_message, &signature).unwrap();
            assert!(!verification);
        }
    }

    #[test]
    fn test_account_signature_compatibility() {
        for i in 0..25 {
            // Sample an Aleo account.
            let private_key = PrivateKey::<Testnet1Parameters>::new(&mut thread_rng());
            let address = Address::<Testnet1Parameters>::from_private_key(&private_key).unwrap();

            // Derive the signature public key.
            let signature_private_key = (private_key.sk_sig, private_key.r_sig);
            let signature_public_key = Testnet1Parameters::account_signature_scheme()
                .generate_public_key(&signature_private_key)
                .unwrap();

            // Ensure the Aleo address matches the signature public key.
            assert_eq!(
                *address.to_bytes_le().unwrap(),
                signature_public_key.to_x_coordinate().to_bytes_le().unwrap()
            );

            // Prepare for signing.
            let rng = ChaChaRng::seed_from_u64(thread_rng().gen());
            let message: Vec<u8> = (0..(32 * i)).map(|_| rand::random::<u8>()).collect();

            // Ensure the Aleo signatures match.
            let expected_signature = private_key.sign(&message, &mut rng.clone()).unwrap();
            let candidate_signature = Testnet1Parameters::account_signature_scheme()
                .sign(&signature_private_key, &message, &mut rng.clone())
                .unwrap();
            assert_eq!(expected_signature, candidate_signature);

            // Ensure the Aleo signatures verify.
            assert!(address.verify_signature(&message, &expected_signature).unwrap());
            assert!(address.verify_signature(&message, &candidate_signature).unwrap());
            assert!(
                Testnet1Parameters::account_signature_scheme()
                    .verify(&signature_public_key, &message, &expected_signature)
                    .unwrap()
            );
            assert!(
                Testnet1Parameters::account_signature_scheme()
                    .verify(&signature_public_key, &message, &candidate_signature)
                    .unwrap()
            );
        }
    }
}

#[cfg(test)]
mod testnet2 {
    use crate::{testnet2::Testnet2Parameters, Account, AccountScheme, Address, Parameters, PrivateKey, ViewKey};
    use snarkvm_algorithms::prelude::*;
    use snarkvm_curves::AffineCurve;
    use snarkvm_utilities::ToBytes;

    use rand::{thread_rng, Rng, SeedableRng};
    use rand_chacha::ChaChaRng;
    use std::{
        convert::{TryFrom, TryInto},
        str::FromStr,
    };

    const ALEO_TESTNET2_PRIVATE_KEY: &str = "APrivateKey1zkp8cC4jgHEBnbtu3xxs1Ndja2EMizcvTRDq5Nikdkukg1p";
    const ALEO_TESTNET2_VIEW_KEY: &str = "AViewKey1mdu8XYL4v8qRkGV2zJAfC4o5mg3qFm71QLPKUqmAnthn";
    const ALEO_TESTNET2_ADDRESS: &str = "aleo13vl8qpz93jal77p7vc0ku87a44x3kul7vffrplgkn2rvtx7kts8sykhp79";

    const ITERATIONS: usize = 1000;

    #[test]
    fn test_account_new() {
        let mut rng = ChaChaRng::seed_from_u64(1231275789u64);

        // Check the seeded derivation matches the hardcoded value, as a sanity check.
        let account = Account::<Testnet2Parameters>::new(&mut rng).unwrap();
        assert_eq!(ALEO_TESTNET2_PRIVATE_KEY, account.private_key().to_string());
        assert_eq!(ALEO_TESTNET2_VIEW_KEY, account.view_key.to_string());
        assert_eq!(ALEO_TESTNET2_ADDRESS, account.address.to_string());

        // Attempt to sample for a new account ITERATIONS times.
        for _ in 0..ITERATIONS {
            assert!(Account::<Testnet2Parameters>::new(&mut rng).is_ok());
        }
    }

    #[test]
    fn test_from_private_key() {
        let private_key = PrivateKey::<Testnet2Parameters>::from_str(ALEO_TESTNET2_PRIVATE_KEY).unwrap();
        let account = Account::<Testnet2Parameters>::try_from(private_key).unwrap();

        assert_eq!(ALEO_TESTNET2_PRIVATE_KEY, account.private_key().to_string());
        assert_eq!(ALEO_TESTNET2_VIEW_KEY, account.view_key.to_string());
        assert_eq!(ALEO_TESTNET2_ADDRESS, account.address.to_string());
    }

    #[test]
    fn test_account_derivation() {
        let private_key = PrivateKey::<Testnet2Parameters>::from_str(ALEO_TESTNET2_PRIVATE_KEY).unwrap();
        let view_key = ViewKey::<Testnet2Parameters>::from_private_key(&private_key).unwrap();
        let address = Address::<Testnet2Parameters>::from_private_key(&private_key).unwrap();

        assert_eq!(ALEO_TESTNET2_PRIVATE_KEY, private_key.to_string());
        assert_eq!(ALEO_TESTNET2_VIEW_KEY, view_key.to_string());
        assert_eq!(ALEO_TESTNET2_ADDRESS, address.to_string());
    }

    #[test]
    fn test_private_key_from_str() {
        let private_key = PrivateKey::<Testnet2Parameters>::from_str(ALEO_TESTNET2_PRIVATE_KEY).unwrap();
        assert_eq!(ALEO_TESTNET2_PRIVATE_KEY, private_key.to_string());
    }

    #[test]
    fn test_private_key_from_invalid_str() {
        assert!(PrivateKey::<Testnet2Parameters>::from_str(ALEO_TESTNET2_VIEW_KEY).is_err());
        assert!(PrivateKey::<Testnet2Parameters>::from_str(ALEO_TESTNET2_ADDRESS).is_err());
        assert!(PrivateKey::<Testnet2Parameters>::from_str("APrivateKey1abcdefghijklmnopqrstuvwxyz").is_err());
        assert!(PrivateKey::<Testnet2Parameters>::from_str("APrivateKey1").is_err());
        assert!(PrivateKey::<Testnet2Parameters>::from_str("").is_err());
    }

    #[test]
    fn test_private_key_into_view_key() {
        let private_key = PrivateKey::<Testnet2Parameters>::from_str(ALEO_TESTNET2_PRIVATE_KEY).unwrap();
        let view_key: ViewKey<_> = private_key.try_into().unwrap();
        assert_eq!(ALEO_TESTNET2_VIEW_KEY, view_key.to_string());
    }

    #[test]
    fn test_view_key_from_str() {
        let view_key = ViewKey::<Testnet2Parameters>::from_str(ALEO_TESTNET2_VIEW_KEY).unwrap();
        assert_eq!(ALEO_TESTNET2_VIEW_KEY, view_key.to_string());
    }

    #[test]
    fn test_view_key_from_invalid_str() {
        assert!(ViewKey::<Testnet2Parameters>::from_str(ALEO_TESTNET2_PRIVATE_KEY).is_err());
        assert!(ViewKey::<Testnet2Parameters>::from_str(ALEO_TESTNET2_ADDRESS).is_err());
        assert!(ViewKey::<Testnet2Parameters>::from_str("AViewKey1abcdefghijklmnopqrstuvwxyz").is_err());
        assert!(ViewKey::<Testnet2Parameters>::from_str("AViewKey1").is_err());
        assert!(ViewKey::<Testnet2Parameters>::from_str("").is_err());
    }

    #[test]
    fn test_private_key_into_address() {
        let private_key = PrivateKey::<Testnet2Parameters>::from_str(ALEO_TESTNET2_PRIVATE_KEY).unwrap();
        let address: Address<_> = private_key.try_into().unwrap();
        assert_eq!(ALEO_TESTNET2_ADDRESS, address.to_string());
    }

    #[test]
    fn test_compute_key_into_address() {
        let private_key = PrivateKey::<Testnet2Parameters>::from_str(ALEO_TESTNET2_PRIVATE_KEY).unwrap();
        let compute_key = private_key.to_compute_key().unwrap();
        let address: Address<_> = compute_key.try_into().unwrap();
        assert_eq!(ALEO_TESTNET2_ADDRESS, address.to_string());
    }

    #[test]
    fn test_view_key_into_address() {
        let view_key = ViewKey::<Testnet2Parameters>::from_str(ALEO_TESTNET2_VIEW_KEY).unwrap();
        let address: Address<_> = view_key.try_into().unwrap();
        assert_eq!(ALEO_TESTNET2_ADDRESS, address.to_string());
    }

    #[test]
    fn test_address_from_str() {
        let address = Address::<Testnet2Parameters>::from_str(ALEO_TESTNET2_ADDRESS).unwrap();
        assert_eq!(ALEO_TESTNET2_ADDRESS, address.to_string());
    }

    #[test]
    fn test_address_from_invalid_str() {
        assert!(Address::<Testnet2Parameters>::from_str(ALEO_TESTNET2_PRIVATE_KEY).is_err());
        assert!(Address::<Testnet2Parameters>::from_str(ALEO_TESTNET2_VIEW_KEY).is_err());
        assert!(Address::<Testnet2Parameters>::from_str("aleo1abcdefghijklmnopqrstuvwxyz").is_err());
        assert!(Address::<Testnet2Parameters>::from_str("aleo1").is_err());
        assert!(Address::<Testnet2Parameters>::from_str("").is_err());
    }

    #[test]
    fn test_account_signatures() {
        let private_key = PrivateKey::<Testnet2Parameters>::from_str(ALEO_TESTNET2_PRIVATE_KEY).unwrap();
        let address = Address::<Testnet2Parameters>::from_private_key(&private_key).unwrap();

        for i in 0..ITERATIONS {
            let message: Vec<u8> = (0..(32 * i)).map(|_| rand::random::<u8>()).collect();
            let signature = private_key.sign(&message, &mut thread_rng()).unwrap();
            let verification = address.verify_signature(&message, &signature).unwrap();
            assert!(verification);
        }
    }

    #[test]
    fn test_invalid_account_signatures() {
        let private_key = PrivateKey::<Testnet2Parameters>::from_str(ALEO_TESTNET2_PRIVATE_KEY).unwrap();
        let address = Address::<Testnet2Parameters>::from_private_key(&private_key).unwrap();

        for i in 0..ITERATIONS {
            let message = "Hi, I'm an Aleo account signature!".as_bytes();
            let incorrect_message: Vec<u8> = (0..(32 * i)).map(|_| rand::random::<u8>()).collect();

            let signature = private_key.sign(&message, &mut thread_rng()).unwrap();
            let verification = address.verify_signature(&incorrect_message, &signature).unwrap();
            assert!(!verification);
        }
    }

    #[test]
    fn test_account_signature_compatibility() {
        for i in 0..25 {
            // Sample an Aleo account.
            let private_key = PrivateKey::<Testnet2Parameters>::new(&mut thread_rng());
            let address = Address::<Testnet2Parameters>::from_private_key(&private_key).unwrap();

            // Derive the signature public key.
            let signature_private_key = (private_key.sk_sig, private_key.r_sig);
            let signature_public_key = Testnet2Parameters::account_signature_scheme()
                .generate_public_key(&signature_private_key)
                .unwrap();

            // Ensure the Aleo address matches the signature public key.
            assert_eq!(
                *address.to_bytes_le().unwrap(),
                signature_public_key.to_x_coordinate().to_bytes_le().unwrap()
            );

            // Prepare for signing.
            let rng = ChaChaRng::seed_from_u64(thread_rng().gen());
            let message: Vec<u8> = (0..(32 * i)).map(|_| rand::random::<u8>()).collect();

            // Ensure the Aleo signatures match.
            let expected_signature = private_key.sign(&message, &mut rng.clone()).unwrap();
            let candidate_signature = Testnet2Parameters::account_signature_scheme()
                .sign(&signature_private_key, &message, &mut rng.clone())
                .unwrap();
            assert_eq!(expected_signature, candidate_signature);

            // Ensure the Aleo signatures verify.
            assert!(address.verify_signature(&message, &expected_signature).unwrap());
            assert!(address.verify_signature(&message, &candidate_signature).unwrap());
            assert!(
                Testnet2Parameters::account_signature_scheme()
                    .verify(&signature_public_key, &message, &expected_signature)
                    .unwrap()
            );
            assert!(
                Testnet2Parameters::account_signature_scheme()
                    .verify(&signature_public_key, &message, &candidate_signature)
                    .unwrap()
            );
        }
    }
}
