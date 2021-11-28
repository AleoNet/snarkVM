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

use crate::{account, Bech32Locator, Network, RecordError};
use snarkvm_algorithms::traits::{EncryptionScheme, CRH};
use snarkvm_utilities::{
    io::{Cursor, Result as IoResult},
    to_bytes_le,
    FromBytes,
    Read,
    ToBytes,
    Write,
};

use anyhow::Result;

#[derive(Derivative)]
#[derivative(
    Clone(bound = "N: Network"),
    Debug(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network"),
    Hash(bound = "N: Network")
)]
pub struct RecordCiphertext<N: Network> {
    ciphertext_randomizer: N::RecordRandomizer,
    record_view_key_commitment: N::RecordViewKeyCommitment,
    record_bytes: Vec<u8>,
}

impl<N: Network> RecordCiphertext<N> {
    /// Returns the record ciphertext object.
    pub fn from(
        ciphertext_randomizer: N::RecordRandomizer,
        record_view_key_commitment: N::RecordViewKeyCommitment,
        record_bytes: Vec<u8>,
    ) -> Result<Self, RecordError> {
        Ok(Self {
            ciphertext_randomizer,
            record_view_key_commitment,
            record_bytes,
        })
    }

    /// Returns the ciphertext randomizer.
    pub fn ciphertext_randomizer(&self) -> N::RecordRandomizer {
        self.ciphertext_randomizer
    }

    /// Returns the record view key commitment.
    pub fn record_view_key_commitment(&self) -> &N::RecordViewKeyCommitment {
        &self.record_view_key_commitment
    }

    /// Returns the record commitment.
    pub fn to_commitment(&self) -> Result<N::Commitment, RecordError> {
        Ok(N::commitment_scheme()
            .hash(&to_bytes_le![
                self.ciphertext_randomizer,
                self.record_view_key_commitment,
                self.record_bytes
            ]?)?
            .into())
    }

    /// Returns the plaintext corresponding to the record ciphertext.
    pub fn to_plaintext(&self, record_view_key: &N::RecordViewKey) -> Result<Vec<u8>, RecordError> {
        // Decrypt the record ciphertext.
        Ok(N::account_encryption_scheme().decrypt(record_view_key, &self.record_bytes)?)
    }

    /// Does the ciphertext encrypt the public key?
    pub fn to_plaintext_if_account_matches(
        &self,
        account: account::Address<N>,
        account_view_key: &account::ViewKey<N>,
    ) -> Option<Vec<u8>> {
        let record_view_key = N::account_encryption_scheme()
            .generate_symmetric_key(&account_view_key, *self.ciphertext_randomizer)
            .unwrap();

        let decryption_result = N::account_encryption_scheme().decrypt_while(&record_view_key, &self.record_bytes);
        match decryption_result {
            Ok(msg) => Some(msg),
            Err(snarkvm_algorithms::EncryptionError::MismatchingAddress) => None,
            Err(e) => panic!("Encountered decryption error: {}", e),
        }
    }
}

impl<N: Network> FromBytes for RecordCiphertext<N> {
    /// Decode the ciphertext into the ciphertext randomizer, record view key commitment, and record ciphertext.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let mut ciphertext = vec![0u8; N::RECORD_CIPHERTEXT_SIZE_IN_BYTES];
        reader.read_exact(&mut ciphertext)?;

        // Decode the ciphertext bytes.
        let mut cursor = Cursor::new(ciphertext);
        let ciphertext_randomizer = N::RecordRandomizer::read_le(&mut cursor)?;
        let record_view_key_commitment = N::RecordViewKeyCommitment::read_le(&mut cursor)?;

        let mut record_bytes = vec![
            0u8;
            N::RECORD_CIPHERTEXT_SIZE_IN_BYTES
                - N::RecordRandomizer::data_size_in_bytes()
                - N::RecordViewKeyCommitment::data_size_in_bytes()
        ];
        cursor.read_exact(&mut record_bytes)?;

        Ok(Self::from(
            ciphertext_randomizer,
            record_view_key_commitment,
            record_bytes,
        )?)
    }
}

impl<N: Network> ToBytes for RecordCiphertext<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.ciphertext_randomizer.write_le(&mut writer)?;
        self.record_view_key_commitment.write_le(&mut writer)?;
        self.record_bytes.write_le(&mut writer)
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::testnet2::Testnet2;
//     use snarkvm_utilities::UniformRand;
//
//     use rand::thread_rng;
//
//     #[test]
//     fn test_serde_json() {
//         let rng = &mut thread_rng();
//
//         let expected_ciphertext = RecordCiphertext::<Testnet2>::from(
//             (0..Testnet2::RECORD_CIPHERTEXT_SIZE_IN_BYTES)
//                 .map(|_| u8::rand(rng))
//                 .collect::<Vec<u8>>(),
//         );
//
//         // Serialize
//         let expected_string = &expected_ciphertext.to_string();
//         let candidate_string = serde_json::to_string(&expected_ciphertext).unwrap();
//         assert_eq!(
//             expected_string,
//             serde_json::Value::from_str(&candidate_string)
//                 .unwrap()
//                 .as_str()
//                 .unwrap()
//         );
//
//         // Deserialize
//         assert_eq!(
//             expected_ciphertext,
//             RecordCiphertext::from_str(&expected_string).unwrap()
//         );
//         assert_eq!(expected_ciphertext, serde_json::from_str(&candidate_string).unwrap());
//     }
//
//     #[test]
//     fn test_bincode() {
//         let rng = &mut thread_rng();
//
//         let expected_ciphertext = RecordCiphertext::<Testnet2>::from_vec(
//             (0..Testnet2::RECORD_CIPHERTEXT_SIZE_IN_BYTES)
//                 .map(|_| u8::rand(rng))
//                 .collect::<Vec<u8>>(),
//         );
//
//         // Serialize
//         let expected_bytes = expected_ciphertext.to_bytes_le().unwrap();
//         assert_eq!(
//             &expected_bytes[..],
//             &bincode::serialize(&expected_ciphertext).unwrap()[..]
//         );
//
//         // Deserialize
//         assert_eq!(
//             expected_ciphertext,
//             RecordCiphertext::read_le(&expected_bytes[..]).unwrap()
//         );
//         assert_eq!(expected_ciphertext, bincode::deserialize(&expected_bytes[..]).unwrap());
//     }
// }
