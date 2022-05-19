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

mod decrypt;
mod encrypt;
mod to_data_id;

use crate::{Address, Network, ViewKey};
use snarkvm_circuits_environment::Mode;
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{FromBits, ToBits};

use anyhow::{bail, Result};
use itertools::Itertools;

/// A general purpose data structure for representing program data in a record.
pub trait DataType: Clone + ToBits + FromBits {}

#[derive(Clone)]
pub enum Data<N: Network, D: DataType> {
    /// Publicly-visible data.
    Plaintext(D, Mode),
    /// Private data encrypted under the account owner's address.
    Ciphertext(Vec<N::Field>, Mode),
}

impl<N: Network, D: DataType> Data<N, D> {
    /// Returns the mode of the data.
    pub fn mode(&self) -> Mode {
        match self {
            Self::Plaintext(_, mode) => *mode,
            Self::Ciphertext(_, mode) => *mode,
        }
    }

    /// Returns `true` if the enum variant corresponds to the correct mode.
    /// Otherwise, the method returns `false`.
    pub fn is_valid(&self) -> bool {
        match self {
            Self::Plaintext(_, mode) => mode.is_constant() || mode.is_public(),
            Self::Ciphertext(_, mode) => mode.is_private(),
        }
    }
}

// #[cfg(test)]
// mod tests {
//     use crate::{ViewKey, Address, PrivateKey};
//     use snarkvm_curves::edwards_bls12::{EdwardsParameters, Fq};
//     use snarkvm_fields::One;
//     use snarkvm_utilities::{test_crypto_rng, FromBytes, ToBytes};
//
//     use core::ops::AddAssign;
//     use rand::Rng;
//
//     pub const ITERATIONS: usize = 1000;
//
//     #[test]
//     fn test_encrypt_and_decrypt() -> Result<()> {
//         // Generate an address, view key, and private key.
//         let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
//         let view_key = ViewKey::try_from(&private_key)?;
//         let address = Address::try_from(&private_key)?;
//
//         let (_randomness, _ciphertext_randomizer, symmetric_key) = encryption.generate_asymmetric_key(&public_key, rng);
//
//         let number_of_bytes = 320;
//         let message = (0..number_of_bytes).map(|_| rand::random::<u8>()).collect::<Vec<u8>>();
//         let encoded_message = TestEncryptionScheme::encode_message(&message).unwrap();
//         let ciphertext = encryption.encrypt(&symmetric_key, &encoded_message);
//         dbg!(ciphertext.len());
//
//         let candidate_message = encryption.decrypt(&symmetric_key, &ciphertext);
//         let decoded_message = TestEncryptionScheme::decode_message(&candidate_message).unwrap();
//         assert_eq!(message, decoded_message);
//
//         Ok(())
//     }
//
//     #[test]
//     fn test_encryption_symmetric_key_commitment() -> Result<()> {
//         // Generate an address, view key, and private key.
//         let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
//         let view_key = ViewKey::try_from(&private_key)?;
//         let address = Address::try_from(&private_key)?;
//
//         let (_randomness, ciphertext_randomizer, symmetric_key) = encryption.generate_asymmetric_key(&public_key, rng);
//         let symmetric_key_commitment = encryption.generate_symmetric_key_commitment(&symmetric_key);
//
//         {
//             // Sanity check that the symmetric key matches, when derived from the private key.
//             let candidate_symmetric_key =
//                 encryption.generate_symmetric_key(&private_key, ciphertext_randomizer).unwrap();
//             assert_eq!(symmetric_key, candidate_symmetric_key);
//         }
//         {
//             // Sanity check that the symmetric key commitment is deterministic.
//             let candidate_symmetric_key_commitment = encryption.generate_symmetric_key_commitment(&symmetric_key);
//             assert_eq!(symmetric_key_commitment, candidate_symmetric_key_commitment);
//         }
//
//         // Ensure different symmetric keys for the same public key fail to match the symmetric key commitment.
//         for _ in 0..ITERATIONS {
//             let (_randomness, _ciphertext_randomizer, alternate_symmetric_key) =
//                 encryption.generate_asymmetric_key(&public_key, rng);
//             let candidate_symmetric_key_commitment =
//                 encryption.generate_symmetric_key_commitment(&alternate_symmetric_key);
//             assert_ne!(symmetric_key_commitment, candidate_symmetric_key_commitment);
//         }
//
//         // Ensure different private keys fail to match the symmetric key commitment.
//         for _ in 0..ITERATIONS {
//             let alternate_private_key = encryption.generate_private_key(rng);
//             let alternate_public_key = encryption.generate_public_key(&alternate_private_key);
//             let (_randomness, _ciphertext_randomizer, alternate_symmetric_key) =
//                 encryption.generate_asymmetric_key(&alternate_public_key, rng);
//             let candidate_symmetric_key_commitment =
//                 encryption.generate_symmetric_key_commitment(&alternate_symmetric_key);
//             assert_ne!(symmetric_key_commitment, candidate_symmetric_key_commitment);
//         }
//
//         Ok(())
//     }
//
//     #[test]
//     fn test_ciphertext_random_manipulation() -> Result<()> {
//         // Generate an address, view key, and private key.
//         let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
//         let view_key = ViewKey::try_from(&private_key)?;
//         let address = Address::try_from(&private_key)?;
//
//         let (_randomness, _ciphertext_randomizer, symmetric_key) = encryption.generate_asymmetric_key(&address, rng);
//
//         let number_of_bytes = 320;
//         let message = (0..number_of_bytes).map(|_| rand::random::<u8>()).collect::<Vec<u8>>();
//         let encoded_message = TestEncryptionScheme::encode_message(&message).unwrap();
//         let ciphertext = encryption.encrypt(&symmetric_key, &encoded_message);
//         dbg!(ciphertext.len());
//
//         let candidate_message = encryption.decrypt(&symmetric_key, &ciphertext);
//         let decoded_message = TestEncryptionScheme::decode_message(&candidate_message).unwrap();
//         assert_eq!(message, decoded_message);
//
//         // Ensure any mutation fails to match the original message.
//         for _ in 0..ITERATIONS {
//             // Copy the ciphertext.
//             let mut ciphertext = ciphertext.clone();
//
//             // Mutate one of the ciphertext elements.
//             let x = rng.gen_range(0..5);
//             ciphertext[x].add_assign(Fq::one());
//
//             // This should fail.
//             let candidate_message = encryption.decrypt(&symmetric_key, &ciphertext);
//             let decoded_message = TestEncryptionScheme::decode_message(&candidate_message).unwrap();
//             assert_ne!(message, decoded_message);
//         }
//
//         Ok(())
//     }
// }
