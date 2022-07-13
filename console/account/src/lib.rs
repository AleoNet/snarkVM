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

#![forbid(unsafe_code)]
#![allow(clippy::too_many_arguments)]

pub use snarkvm_console_types::{environment::prelude::*, Address, Field, Group, Scalar};

pub mod address;

#[cfg(feature = "compute_key")]
pub mod compute_key;
#[cfg(feature = "compute_key")]
pub use compute_key::*;

#[cfg(feature = "private_key")]
pub mod private_key;
#[cfg(feature = "private_key")]
pub use private_key::*;

#[cfg(feature = "signature")]
pub mod signature;
#[cfg(feature = "signature")]
pub use signature::*;

#[cfg(feature = "view_key")]
pub mod view_key;
#[cfg(feature = "view_key")]
pub use view_key::*;

// #[cfg(test)]
// mod tests {
//     use crate::{testnet2::Testnet2, Account, Address, Network, PrivateKey, ViewKey};
//     use snarkvm_algorithms::prelude::*;
//
//     use rand::{thread_rng, Rng, SeedableRng};
//     use rand_chacha::ChaChaRng;
//     use std::str::FromStr;
//
//     const ALEO_PRIVATE_KEY: &str = "APrivateKey1zkp8cC4jgHEBnbtu3xxs1Ndja2EMizcvTRDq5Nikdkukg1p";
//     const ALEO_VIEW_KEY: &str = "AViewKey1iAf6a7fv6ELA4ECwAth1hDNUJJNNoWNThmREjpybqder";
//     const ALEO_ADDRESS: &str = "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah";
//
//     const ITERATIONS: usize = 1000;
//
//     #[test]
//     fn test_account_new() {
//         let mut rng = ChaChaRng::seed_from_u64(1231275789u64);
//
//         // Check the seeded derivation matches the hardcoded value, as a sanity check.
//         let account = Account::<Testnet2>::new(&mut rng);
//         assert_eq!(ALEO_PRIVATE_KEY, account.private_key().to_string());
//         assert_eq!(ALEO_VIEW_KEY, account.view_key().to_string());
//         assert_eq!(ALEO_ADDRESS, account.address().to_string());
//
//         // Attempt to sample for a new account ITERATIONS times.
//         for _ in 0..ITERATIONS {
//             assert!(Account::<Testnet2>::new(&mut rng).private_key().is_valid());
//         }
//     }
//
//     #[test]
//     fn test_from_private_key() {
//         let private_key = PrivateKey::<Testnet2>::from_str(ALEO_PRIVATE_KEY).unwrap();
//         let account = Account::<Testnet2>::from(private_key);
//
//         assert_eq!(ALEO_PRIVATE_KEY, account.private_key().to_string());
//         assert_eq!(ALEO_VIEW_KEY, account.view_key().to_string());
//         assert_eq!(ALEO_ADDRESS, account.address().to_string());
//     }
//
//     #[test]
//     fn test_account_derivation() {
//         let private_key = PrivateKey::<Testnet2>::from_str(ALEO_PRIVATE_KEY).unwrap();
//         let view_key = ViewKey::<Testnet2>::from_private_key(&private_key);
//         let address = Address::<Testnet2>::from_private_key(&private_key);
//
//         assert_eq!(ALEO_PRIVATE_KEY, private_key.to_string());
//         assert_eq!(ALEO_VIEW_KEY, view_key.to_string());
//         assert_eq!(ALEO_ADDRESS, address.to_string());
//     }
//
//     #[test]
//     fn test_private_key_from_str() {
//         let private_key = PrivateKey::<Testnet2>::from_str(ALEO_PRIVATE_KEY).unwrap();
//         assert_eq!(ALEO_PRIVATE_KEY, private_key.to_string());
//     }
//
//     #[test]
//     fn test_private_key_from_invalid_str() {
//         assert!(PrivateKey::<Testnet2>::from_str(ALEO_VIEW_KEY).is_err());
//         assert!(PrivateKey::<Testnet2>::from_str(ALEO_ADDRESS).is_err());
//         assert!(PrivateKey::<Testnet2>::from_str("APrivateKey1abcdefghijklmnopqrstuvwxyz").is_err());
//         assert!(PrivateKey::<Testnet2>::from_str("APrivateKey1").is_err());
//         assert!(PrivateKey::<Testnet2>::from_str("").is_err());
//     }
//
//     #[test]
//     fn test_private_key_into_view_key() {
//         let private_key = PrivateKey::<Testnet2>::from_str(ALEO_PRIVATE_KEY).unwrap();
//         let view_key: ViewKey<_> = private_key.into();
//         assert_eq!(ALEO_VIEW_KEY, view_key.to_string());
//     }
//
//     #[test]
//     fn test_view_key_from_str() {
//         let view_key = ViewKey::<Testnet2>::from_str(ALEO_VIEW_KEY).unwrap();
//         assert_eq!(ALEO_VIEW_KEY, view_key.to_string());
//     }
//
//     #[test]
//     fn test_view_key_from_invalid_str() {
//         assert!(ViewKey::<Testnet2>::from_str(ALEO_PRIVATE_KEY).is_err());
//         assert!(ViewKey::<Testnet2>::from_str(ALEO_ADDRESS).is_err());
//         assert!(ViewKey::<Testnet2>::from_str("AViewKey1abcdefghijklmnopqrstuvwxyz").is_err());
//         assert!(ViewKey::<Testnet2>::from_str("AViewKey1").is_err());
//         assert!(ViewKey::<Testnet2>::from_str("").is_err());
//     }
//
//     #[test]
//     fn test_private_key_into_address() {
//         let private_key = PrivateKey::<Testnet2>::from_str(ALEO_PRIVATE_KEY).unwrap();
//         let address: Address<_> = private_key.into();
//         assert_eq!(ALEO_ADDRESS, address.to_string());
//     }
//
//     #[test]
//     fn test_compute_key_into_address() {
//         let private_key = PrivateKey::<Testnet2>::from_str(ALEO_PRIVATE_KEY).unwrap();
//         let compute_key = private_key.to_compute_key();
//         let address: Address<_> = compute_key.into();
//         assert_eq!(ALEO_ADDRESS, address.to_string());
//     }
//
//     #[test]
//     fn test_view_key_into_address() {
//         let view_key = ViewKey::<Testnet2>::from_str(ALEO_VIEW_KEY).unwrap();
//         let address: Address<_> = view_key.into();
//         assert_eq!(ALEO_ADDRESS, address.to_string());
//     }
//
//     #[test]
//     fn test_address_from_str() {
//         let address = Address::<Testnet2>::from_str(ALEO_ADDRESS).unwrap();
//         assert_eq!(ALEO_ADDRESS, address.to_string());
//     }
//
//     #[test]
//     fn test_address_from_invalid_str() {
//         assert!(Address::<Testnet2>::from_str(ALEO_PRIVATE_KEY).is_err());
//         assert!(Address::<Testnet2>::from_str(ALEO_VIEW_KEY).is_err());
//         assert!(Address::<Testnet2>::from_str("aleo1abcdefghijklmnopqrstuvwxyz").is_err());
//         assert!(Address::<Testnet2>::from_str("aleo1").is_err());
//         assert!(Address::<Testnet2>::from_str("").is_err());
//     }
//
//     #[test]
//     fn test_account_signatures() {
//         let private_key = PrivateKey::<Testnet2>::from_str(ALEO_PRIVATE_KEY).unwrap();
//         let address = Address::<Testnet2>::from_private_key(&private_key);
//
//         for i in 0..ITERATIONS {
//             let message: Vec<bool> = (0..(32 * i)).map(|_| bool::rand(&mut test_rng())).collect();
//             let signature = private_key.sign(&message, &mut thread_rng()).unwrap();
//             let verification = address.verify_signature(&message, &signature).unwrap();
//             assert!(verification);
//         }
//     }
//
//     #[test]
//     fn test_invalid_account_signatures() {
//         let private_key = PrivateKey::<Testnet2>::from_str(ALEO_PRIVATE_KEY).unwrap();
//         let address = Address::<Testnet2>::from_private_key(&private_key);
//
//         for i in 0..ITERATIONS {
//             let message = "Hi, I'm an Aleo account signature!".as_bytes().to_bits_le();
//             let incorrect_message: Vec<bool> = (0..(32 * i)).map(|_| bool::rand(&mut test_rng())).collect();
//
//             let signature = private_key.sign(&message, &mut thread_rng()).unwrap();
//             let verification = address.verify_signature(&incorrect_message, &signature).unwrap();
//             assert!(!verification);
//         }
//     }
//
//     #[test]
//     fn test_account_signature_compatibility() {
//         for i in 0..25 {
//             // Sample an Aleo account.
//             let private_key = PrivateKey::<Testnet2>::new(&mut thread_rng());
//             let address = Address::<Testnet2>::from_private_key(&private_key);
//
//             // Derive the signature public key.
//             let signature_private_key = (private_key.sk_sig, private_key.r_sig);
//             let signature_public_key = Testnet2::account_signature_scheme().generate_public_key(&signature_private_key);
//
//             // Ensure the Aleo address matches the signature public key.
//             assert_eq!(*address.to_bytes_le().unwrap(), signature_public_key.to_x_coordinate().to_bytes_le().unwrap());
//
//             // Prepare for signing.
//             let rng = ChaChaRng::seed_from_u64(thread_rng().gen());
//             let message: Vec<bool> = (0..(32 * i)).map(|_| bool::rand(&mut test_rng())).collect();
//
//             // Ensure the Aleo signatures match.
//             let expected_signature = private_key.sign(&message, &mut rng.clone()).unwrap();
//             let candidate_signature = Testnet2::account_signature_scheme()
//                 .sign(&signature_private_key, &message, &mut rng.clone())
//                 .unwrap()
//                 .into();
//             assert_eq!(expected_signature, candidate_signature);
//
//             // Ensure the Aleo signatures verify.
//             assert!(address.verify_signature(&message, &expected_signature).unwrap());
//             assert!(address.verify_signature(&message, &candidate_signature).unwrap());
//             assert!(
//                 Testnet2::account_signature_scheme()
//                     .verify(&signature_public_key, &message, &expected_signature)
//                     .unwrap()
//             );
//             assert!(
//                 Testnet2::account_signature_scheme()
//                     .verify(&signature_public_key, &message, &candidate_signature)
//                     .unwrap()
//             );
//         }
//     }
//
//     #[test]
//     fn test_aleo_signature_bech32() {
//         for i in 0..25 {
//             // Sample an Aleo account.
//             let private_key = PrivateKey::<Testnet2>::new(&mut thread_rng());
//
//             // Craft the Aleo signature.
//             let message: Vec<bool> = (0..(32 * i)).map(|_| bool::rand(&mut test_rng())).collect();
//             let expected_signature = private_key.sign(&message, &mut thread_rng()).unwrap();
//
//             let candidate_string = &expected_signature.to_string();
//             assert_eq!(216, candidate_string.len(), "Update me if serialization has changed");
//             assert_eq!("sign1", &candidate_string[0..5], "Update me if the prefix has changed");
//         }
//     }
//
//     #[test]
//     fn test_aleo_signature_serde_json() {
//         for i in 0..25 {
//             // Sample an Aleo account.
//             let private_key = PrivateKey::<Testnet2>::new(&mut thread_rng());
//
//             // Craft the Aleo signature.
//             let message: Vec<bool> = (0..(32 * i)).map(|_| bool::rand(&mut test_rng())).collect();
//             let expected_signature = private_key.sign(&message, &mut thread_rng()).unwrap();
//
//             // Serialize
//             let expected_string = &expected_signature.to_string();
//             let candidate_string = serde_json::to_string(&expected_signature).unwrap();
//             assert_eq!(expected_string, serde_json::Value::from_str(&candidate_string).unwrap().as_str().unwrap());
//
//             // Deserialize
//             assert_eq!(expected_signature, serde_json::from_str(&candidate_string).unwrap());
//             assert_eq!(expected_signature, <Testnet2 as Network>::AccountSignature::from_str(expected_string).unwrap());
//         }
//     }
//
//     #[test]
//     fn test_aleo_signature_bincode() {
//         for i in 0..25 {
//             // Sample an Aleo account.
//             let private_key = PrivateKey::<Testnet2>::new(&mut thread_rng());
//
//             // Craft the Aleo signature.
//             let message: Vec<bool> = (0..(32 * i)).map(|_| bool::rand(&mut test_rng())).collect();
//             let expected_signature = private_key.sign(&message, &mut thread_rng()).unwrap();
//
//             // Serialize
//             let expected_bytes = expected_signature.to_bytes_le().unwrap();
//             assert_eq!(Testnet2::SIGNATURE_SIZE_IN_BYTES, expected_bytes.len());
//             assert_eq!(&expected_bytes[..], &bincode::serialize(&expected_signature).unwrap()[..]);
//
//             // Deserialize
//             assert_eq!(expected_signature, bincode::deserialize(&expected_bytes[..]).unwrap());
//             assert_eq!(
//                 expected_signature,
//                 <Testnet2 as Network>::AccountSignature::read_le(&expected_bytes[..]).unwrap()
//             );
//         }
//     }
// }
