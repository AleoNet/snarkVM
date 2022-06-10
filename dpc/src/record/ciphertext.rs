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

use crate::{DecryptionKey, Network, RecordError, ViewKey};
use snarkvm_algorithms::traits::{EncryptionScheme, CRH};
use snarkvm_utilities::{error, io::Result as IoResult, to_bytes_le, FromBytes, Read, ToBytes, Write};

use anyhow::{anyhow, Result};
use core::hash::{Hash, Hasher};

#[derive(Clone, Debug)]
pub struct Ciphertext<N: Network> {
    commitment: N::Commitment,
    randomizer: N::RecordRandomizer,
    record_view_key_commitment: N::RecordViewKeyCommitment,
    record_elements: Vec<N::InnerScalarField>,
    program_id: Option<N::ProgramID>,
    is_dummy: bool,
}

impl<N: Network> Ciphertext<N> {
    /// Returns the record ciphertext object.
    pub fn from(
        randomizer: N::RecordRandomizer,
        record_view_key_commitment: N::RecordViewKeyCommitment,
        record_elements: Vec<N::InnerScalarField>,
        program_id: Option<N::ProgramID>,
        is_dummy: bool,
    ) -> Result<Self, RecordError> {
        let program_id_bytes =
            program_id.map_or(Ok(vec![0u8; N::PROGRAM_ID_SIZE_IN_BYTES]), |program_id| program_id.to_bytes_le())?;

        // Compute the commitment.
        let commitment = N::commitment_scheme()
            .hash_bytes(&to_bytes_le![
                randomizer,
                record_view_key_commitment,
                record_elements,
                program_id_bytes,
                is_dummy
            ]?)?
            .into();

        Ok(Self { commitment, randomizer, record_view_key_commitment, record_elements, program_id, is_dummy })
    }

    /// Returns `true` if this ciphertext belongs to the given account view key.
    pub fn is_owner(&self, account_view_key: &ViewKey<N>) -> bool {
        // Compute the record view key.
        let candidate_record_view_key =
            match N::account_encryption_scheme().generate_symmetric_key(account_view_key, *self.randomizer) {
                Some(symmetric_key) => symmetric_key,
                None => return false,
            };

        // Compute the record view key commitment.
        let candidate_record_view_key_commitment =
            N::account_encryption_scheme().generate_symmetric_key_commitment(&candidate_record_view_key);

        // Check if the computed record view key commitment matches.
        *self.record_view_key_commitment == candidate_record_view_key_commitment
    }

    /// Returns the record commitment.
    pub fn commitment(&self) -> N::Commitment {
        self.commitment
    }

    /// Returns the ciphertext randomizer.
    pub fn randomizer(&self) -> N::RecordRandomizer {
        self.randomizer
    }

    /// Returns the record view key commitment.
    pub fn record_view_key_commitment(&self) -> &N::RecordViewKeyCommitment {
        &self.record_view_key_commitment
    }

    /// Returns the program id of this record.
    pub fn program_id(&self) -> Option<N::ProgramID> {
        self.program_id
    }

    /// Returns the plaintext and record view key corresponding to the record ciphertext.
    pub fn to_plaintext(
        &self,
        decryption_key: &DecryptionKey<N>,
    ) -> Result<(Vec<N::InnerScalarField>, N::RecordViewKey)> {
        let record_view_key = match decryption_key {
            DecryptionKey::AccountViewKey(account_view_key) => {
                // Compute the candidate record view key.
                match N::account_encryption_scheme().generate_symmetric_key(account_view_key, *self.randomizer) {
                    Some(candidate_record_view_key) => candidate_record_view_key.into(),
                    None => return Err(anyhow!("The given account view key does not correspond to this ciphertext")),
                }
            }
            DecryptionKey::RecordViewKey(record_view_key) => record_view_key.clone(),
        };

        // Compute the record view key commitment.
        let candidate_record_view_key_commitment =
            N::account_encryption_scheme().generate_symmetric_key_commitment(&record_view_key);

        // Check if the computed record view key commitment matches.
        match *self.record_view_key_commitment == candidate_record_view_key_commitment {
            // Decrypt the record ciphertext.
            true => {
                let plaintext = N::account_encryption_scheme().decrypt(&record_view_key, &self.record_elements);
                Ok((plaintext, record_view_key))
            }
            false => Err(anyhow!("The given record view key does not correspond to this ciphertext")),
        }
    }
}

impl<N: Network> PartialEq for Ciphertext<N> {
    fn eq(&self, other: &Self) -> bool {
        self.commitment == other.commitment
    }
}

impl<N: Network> Eq for Ciphertext<N> {}

impl<N: Network> Hash for Ciphertext<N> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.commitment.hash(state);
    }
}

impl<N: Network> FromBytes for Ciphertext<N> {
    /// Decode the ciphertext into the ciphertext randomizer, record view key commitment, and record ciphertext.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Decode the ciphertext bytes.
        let ciphertext_randomizer = N::RecordRandomizer::read_le(&mut reader)?;
        let record_view_key_commitment = N::RecordViewKeyCommitment::read_le(&mut reader)?;

        // Decode the number of ciphertext elements.
        let num_elements: u16 = FromBytes::read_le(&mut reader)?;

        let mut record_elements = Vec::with_capacity(num_elements as usize);
        for _ in 0..num_elements {
            record_elements.push(FromBytes::read_le(&mut reader)?);
        }

        let program_id_exists: bool = FromBytes::read_le(&mut reader)?;
        let program_id: Option<N::ProgramID> = match program_id_exists {
            true => Some(FromBytes::read_le(&mut reader)?),
            false => None,
        };

        let is_dummy: bool = FromBytes::read_le(&mut reader)?;

        Ok(Self::from(ciphertext_randomizer, record_view_key_commitment, record_elements, program_id, is_dummy)?)
    }
}

impl<N: Network> ToBytes for Ciphertext<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.randomizer.write_le(&mut writer)?;
        self.record_view_key_commitment.write_le(&mut writer)?;

        // Ensure the number of elements is within bounds.
        if self.record_elements.len() > (u16::MAX as usize) {
            return Err(error(format!("The number of ciphertext elements cannot exceed {} elements", u16::MAX)));
        }

        (self.record_elements.len() as u16).write_le(&mut writer)?;
        for element in &self.record_elements {
            element.write_le(&mut writer)?;
        }

        match &self.program_id {
            Some(program_id) => {
                true.write_le(&mut writer)?;
                program_id.write_le(&mut writer)?
            }
            None => false.write_le(&mut writer)?,
        }

        self.is_dummy.write_le(&mut writer)
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::testnet2::Testnet2;
//     use snarkvm_utilities::Uniform;
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
