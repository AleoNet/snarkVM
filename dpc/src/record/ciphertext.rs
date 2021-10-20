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

use crate::{Address, Network, Payload, Record, RecordError, ViewKey};
use snarkvm_algorithms::traits::{EncryptionScheme, CRH};
use snarkvm_utilities::{
    fmt,
    io::{Cursor, Result as IoResult},
    marker::PhantomData,
    str::FromStr,
    to_bytes_le,
    FromBytes,
    FromBytesDeserializer,
    Read,
    ToBytes,
    ToBytesSerializer,
    Write,
};

use anyhow::{anyhow, Result};
use rand::{thread_rng, CryptoRng, Rng};
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

#[derive(Derivative)]
#[derivative(
    Clone(bound = "N: Network"),
    Debug(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network"),
    Hash(bound = "N: Network")
)]
pub struct RecordCiphertext<N: Network> {
    ciphertext: Vec<u8>,
    phantom: PhantomData<N>,
}

impl<N: Network> RecordCiphertext<N> {
    pub fn from_vec(ciphertext: Vec<u8>) -> Self {
        assert_eq!(N::CIPHERTEXT_SIZE_IN_BYTES, ciphertext.len());
        Self {
            ciphertext,
            phantom: PhantomData,
        }
    }

    /// Encrypt the given vector of records and returns
    /// 1. Encrypted record
    /// 2. Encryption randomness
    pub fn encrypt<R: Rng + CryptoRng>(
        record: &Record<N>,
        rng: &mut R,
    ) -> Result<(
        Self,
        <<N as Network>::AccountEncryptionScheme as EncryptionScheme>::Randomness,
    )> {
        // Convert the record into bytes.
        let buffer = to_bytes_le![
            record.value(),
            record.payload(),
            record.program_id(),
            record.serial_number_nonce(),
            record.commitment_randomness()
        ]?;

        // Ensure the record bytes are within the permitted size.
        if buffer.len() > u16::MAX as usize {
            return Err(anyhow!("Records must be <= 65535 bytes, found {} bytes", buffer.len()));
        }

        // Encrypt the record bytes.
        let randomizer = N::account_encryption_scheme().generate_randomness(rng);
        let ciphertext = N::account_encryption_scheme().encrypt(&*record.owner(), &randomizer, &buffer)?;

        Ok((Self::from_vec(ciphertext), randomizer))
    }

    /// Decrypt the record ciphertext using the view key of the recipient.
    pub fn decrypt(&self, recipient_view_key: &ViewKey<N>) -> Result<Record<N>> {
        // Decrypt the record ciphertext.
        let plaintext = N::account_encryption_scheme().decrypt(&*recipient_view_key, &self.ciphertext)?;

        let mut cursor = Cursor::new(plaintext);

        // Deserialize the plaintext bytes.
        let value = u64::read_le(&mut cursor)?;
        let payload = Payload::read_le(&mut cursor)?;
        let program_id = N::ProgramID::read_le(&mut cursor)?;
        let serial_number_nonce = N::SerialNumber::read_le(&mut cursor)?;
        let commitment_randomness = N::CommitmentRandomness::read_le(&mut cursor)?;

        // Derive the record owner.
        let owner = Address::from_view_key(&recipient_view_key);

        Ok(Record::from(
            owner,
            value,
            payload,
            program_id,
            serial_number_nonce,
            commitment_randomness,
        )?)
    }

    /// Returns the record ciphertext ID. The preimage is the ciphertext x-coordinates appended with the selector bits.
    pub fn to_ciphertext_id(&self) -> Result<N::CiphertextID> {
        Ok(N::ciphertext_id_crh().hash(&self.ciphertext)?)
    }
}

impl<N: Network> FromBytes for RecordCiphertext<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let mut ciphertext = Vec::with_capacity(N::CIPHERTEXT_SIZE_IN_BYTES);
        for _ in 0..N::CIPHERTEXT_SIZE_IN_BYTES {
            ciphertext.push(u8::read_le(&mut reader)?);
        }

        Ok(Self::from_vec(ciphertext))
    }
}

impl<N: Network> ToBytes for RecordCiphertext<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.ciphertext.write_le(&mut writer)
    }
}

impl<N: Network> FromStr for RecordCiphertext<N> {
    type Err = RecordError;

    fn from_str(payload_hex: &str) -> Result<Self, Self::Err> {
        Ok(Self::from_bytes_le(&hex::decode(payload_hex)?)?)
    }
}

impl<N: Network> fmt::Display for RecordCiphertext<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let bytes = self.to_bytes_le().expect("Failed to convert ciphertext to bytes");
        write!(f, "{}", hex::encode(bytes))
    }
}

impl<N: Network> Serialize for RecordCiphertext<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => serializer.collect_str(self),
            false => ToBytesSerializer::serialize(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for RecordCiphertext<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => {
                FromBytesDeserializer::<Self>::deserialize(deserializer, "ciphertext", N::CIPHERTEXT_SIZE_IN_BYTES)
            }
        }
    }
}

impl<N: Network> Default for RecordCiphertext<N> {
    fn default() -> Self {
        let (record, _randomness) = Self::encrypt(&Record::default(), &mut thread_rng()).unwrap();
        record
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testnet2::Testnet2;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    #[test]
    fn test_serde_json() {
        let rng = &mut thread_rng();

        let expected_ciphertext = RecordCiphertext::<Testnet2>::from_vec(
            (0..Testnet2::CIPHERTEXT_SIZE_IN_BYTES)
                .map(|_| u8::rand(rng))
                .collect::<Vec<u8>>(),
        );

        // Serialize
        let expected_string = &expected_ciphertext.to_string();
        let candidate_string = serde_json::to_string(&expected_ciphertext).unwrap();
        assert_eq!(
            expected_string,
            serde_json::Value::from_str(&candidate_string)
                .unwrap()
                .as_str()
                .unwrap()
        );

        // Deserialize
        assert_eq!(
            expected_ciphertext,
            RecordCiphertext::from_str(&expected_string).unwrap()
        );
        assert_eq!(expected_ciphertext, serde_json::from_str(&candidate_string).unwrap());
    }

    #[test]
    fn test_bincode() {
        let rng = &mut thread_rng();

        let expected_ciphertext = RecordCiphertext::<Testnet2>::from_vec(
            (0..Testnet2::CIPHERTEXT_SIZE_IN_BYTES)
                .map(|_| u8::rand(rng))
                .collect::<Vec<u8>>(),
        );

        // Serialize
        let expected_bytes = expected_ciphertext.to_bytes_le().unwrap();
        assert_eq!(
            &expected_bytes[..],
            &bincode::serialize(&expected_ciphertext).unwrap()[..]
        );

        // Deserialize
        assert_eq!(
            expected_ciphertext,
            RecordCiphertext::read_le(&expected_bytes[..]).unwrap()
        );
        assert_eq!(expected_ciphertext, bincode::deserialize(&expected_bytes[..]).unwrap());
    }
}
