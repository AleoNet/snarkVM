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

use crate::{Address, AleoAmount, Bech32Locator, Ciphertext, ComputeKey, Network, Payload, RecordError, ViewKey};
use snarkvm_algorithms::traits::{EncryptionScheme, PRF};
use snarkvm_utilities::{to_bytes_le, FromBytes, FromBytesDeserializer, ToBytes, ToBytesSerializer};

use anyhow::anyhow;
use rand::{CryptoRng, Rng};
use serde::{de, ser::SerializeStruct, Deserialize, Deserializer, Serialize, Serializer};
use std::{
    fmt,
    io::{Cursor, Read, Result as IoResult, Write},
    ops::Deref,
    str::FromStr,
};

#[derive(Derivative)]
#[derivative(
    Debug(bound = "N: Network"),
    Clone(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network")
)]
pub struct Record<N: Network> {
    owner: Address<N>,
    value: AleoAmount,
    payload: Payload<N>,
    program_id: N::ProgramID,
    record_view_key: N::RecordViewKey,
    ciphertext: N::RecordCiphertext,
}

impl<N: Network> Record<N> {
    /// Returns a new noop record.
    pub fn new_noop<R: Rng + CryptoRng>(owner: Address<N>, rng: &mut R) -> Result<Self, RecordError> {
        Self::new(
            owner,
            AleoAmount::ZERO,
            Payload::<N>::default(),
            *N::noop_program_id(),
            rng,
        )
    }

    /// Returns a new record.
    pub fn new<R: Rng + CryptoRng>(
        owner: Address<N>,
        value: AleoAmount,
        payload: Payload<N>,
        program_id: N::ProgramID,
        rng: &mut R,
    ) -> Result<Self, RecordError> {
        // Generate the ciphertext parameters.
        let (_randomness, randomizer, record_view_key) =
            N::account_encryption_scheme().generate_asymmetric_key(&*owner, rng);
        Self::from(
            owner,
            value,
            payload,
            program_id,
            randomizer.into(),
            record_view_key.into(),
        )
    }

    /// Returns a record from the given inputs.
    pub fn from(
        owner: Address<N>,
        value: AleoAmount,
        payload: Payload<N>,
        program_id: N::ProgramID,
        randomizer: N::RecordRandomizer,
        record_view_key: N::RecordViewKey,
    ) -> Result<Self, RecordError> {
        // Encode the record contents into plaintext bytes.
        let plaintext = Self::encode_plaintext(owner, value, &payload, program_id)?;

        // Encrypt the record bytes.
        let ciphertext = Ciphertext::<N>::from(
            randomizer,
            N::account_encryption_scheme()
                .generate_symmetric_key_commitment(&record_view_key)
                .into(),
            N::account_encryption_scheme().encrypt(&record_view_key, &plaintext)?,
        )?;

        Ok(Self {
            owner,
            value,
            payload,
            program_id,
            record_view_key,
            ciphertext: ciphertext.into(),
        })
    }

    /// Returns a record from the given account view key and ciphertext.
    pub fn from_account_view_key(
        account_view_key: &ViewKey<N>,
        ciphertext: &N::RecordCiphertext,
    ) -> Result<Self, RecordError> {
        // Compute the record view key.
        let record_view_key = match N::account_encryption_scheme()
            .generate_symmetric_key(&*account_view_key, *ciphertext.deref().randomizer())
        {
            Some(record_view_key) => record_view_key.into(),
            None => return Err(anyhow!("Failed to compute record view key due to malformed account view key").into()),
        };

        // Decrypt the record ciphertext.
        let plaintext = ciphertext.deref().to_plaintext(&record_view_key)?;
        let (owner, value, payload, program_id) = Self::decode_plaintext(&plaintext)?;

        // Ensure the record owner matches.
        let expected_owner = Address::from_view_key(account_view_key);
        match owner == expected_owner {
            true => Ok(Self {
                owner,
                value,
                payload,
                program_id,
                record_view_key,
                ciphertext: ciphertext.clone(),
            }),
            false => Err(anyhow!("Decoded incorrect record owner from ciphertext").into()),
        }
    }

    /// Returns a record from the given record view key and ciphertext.
    pub fn from_record_view_key(
        record_view_key: N::RecordViewKey,
        ciphertext: &N::RecordCiphertext,
    ) -> Result<Self, RecordError> {
        // Decrypt the record ciphertext.
        let plaintext = ciphertext.deref().to_plaintext(&record_view_key)?;
        let (owner, value, payload, program_id) = Self::decode_plaintext(&plaintext)?;

        Ok(Self {
            owner,
            value,
            payload,
            program_id,
            record_view_key,
            ciphertext: ciphertext.clone(),
        })
    }

    /// Returns `true` if the record is a dummy.
    pub fn is_dummy(&self) -> bool {
        self.value.is_zero() && self.payload.is_empty() && self.program_id == *N::noop_program_id()
    }

    /// Returns the record owner.
    pub fn owner(&self) -> Address<N> {
        self.owner
    }

    /// Returns the record value.
    pub fn value(&self) -> AleoAmount {
        self.value
    }

    /// Returns the record payload.
    pub fn payload(&self) -> &Payload<N> {
        &self.payload
    }

    /// Returns the program id of this record.
    pub fn program_id(&self) -> N::ProgramID {
        self.program_id
    }

    /// Returns the randomizer used for the ciphertext.
    pub fn randomizer(&self) -> N::RecordRandomizer {
        self.ciphertext.deref().randomizer()
    }

    /// Returns the view key of this record.
    pub fn record_view_key(&self) -> &N::RecordViewKey {
        &self.record_view_key
    }

    /// Returns the commitment of this record.
    pub fn commitment(&self) -> N::Commitment {
        self.ciphertext.deref().commitment()
    }

    /// Returns this record as ciphertext.
    pub fn ciphertext(&self) -> &N::RecordCiphertext {
        &self.ciphertext
    }

    /// Returns the serial number of the record, given the compute key corresponding to the record owner.
    pub fn to_serial_number(&self, compute_key: &ComputeKey<N>) -> Result<N::SerialNumber, RecordError> {
        // Check that the compute key corresponds with the owner of the record.
        if self.owner != Address::<N>::from_compute_key(compute_key) {
            return Err(RecordError::IncorrectComputeKey);
        }

        // Compute the serial number.
        // First, convert the program scalar field element to bytes,
        // and interpret these bytes as a program base field element
        // For our choice of scalar field and base field (i.e., on TE curves)
        // scalar field is always smaller than base field, so the bytes always fit without
        // wraparound.
        let seed = FromBytes::read_le(&compute_key.sk_prf().to_bytes_le()?[..])?;
        let input = self.commitment();
        let serial_number = N::SerialNumberPRF::evaluate(&seed, &input.into())?.into();

        Ok(serial_number)
    }

    /// Encode the record contents into plaintext bytes.
    fn encode_plaintext(
        owner: Address<N>,
        value: AleoAmount,
        payload: &Payload<N>,
        program_id: N::ProgramID,
    ) -> Result<Vec<u8>, RecordError> {
        // Determine if the record is a dummy.
        let is_dummy = value.is_zero() && payload.is_empty() && program_id == *N::noop_program_id();

        // Total = 32 + 1 + 8 + 128 + 48 = 217 bytes
        let plaintext = to_bytes_le![
            owner,      // 256 bits = 32 bytes
            is_dummy,   // 1 bit = 1 byte
            value,      // 64 bits = 8 bytes
            payload,    // 1024 bits = 128 bytes
            program_id  // 384 bits = 48 bytes
        ]?;

        // Ensure the record bytes are within the permitted size.
        match plaintext.len() <= u16::MAX as usize {
            true => Ok(plaintext),
            false => Err(anyhow!("Records must be <= 65535 bytes, found {} bytes", plaintext.len()).into()),
        }
    }

    /// Decode the plaintext bytes into the record contents.
    fn decode_plaintext(
        plaintext: &Vec<u8>,
    ) -> Result<(Address<N>, AleoAmount, Payload<N>, N::ProgramID), RecordError> {
        assert_eq!(
            1 + N::ADDRESS_SIZE_IN_BYTES + 8 + N::RECORD_PAYLOAD_SIZE_IN_BYTES + N::ProgramID::data_size_in_bytes(),
            plaintext.len()
        );

        // Decode the plaintext bytes.
        let mut cursor = Cursor::new(plaintext);
        let owner = Address::<N>::read_le(&mut cursor)?;
        let is_dummy = u8::read_le(&mut cursor)?;
        let value = AleoAmount::read_le(&mut cursor)?;
        let payload = Payload::read_le(&mut cursor)?;
        let program_id = N::ProgramID::read_le(&mut cursor)?;

        // Ensure the dummy flag in the record is correct.
        let expected_dummy = value.is_zero() && payload.is_empty() && program_id == *N::noop_program_id();
        match is_dummy == expected_dummy as u8 {
            true => Ok((owner, value, payload, program_id)),
            false => Err(anyhow!("Decoded incorrect is_dummy flag in record plaintext bytes").into()),
        }
    }
}

impl<N: Network> ToBytes for Record<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.owner.write_le(&mut writer)?;
        self.value.write_le(&mut writer)?;
        self.payload.write_le(&mut writer)?;
        self.program_id.write_le(&mut writer)?;
        self.randomizer().write_le(&mut writer)?;
        self.record_view_key.write_le(&mut writer)
    }
}

impl<N: Network> FromBytes for Record<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let owner: Address<N> = FromBytes::read_le(&mut reader)?;
        let value: AleoAmount = FromBytes::read_le(&mut reader)?;
        let payload: Payload<N> = FromBytes::read_le(&mut reader)?;
        let program_id: N::ProgramID = FromBytes::read_le(&mut reader)?;
        let randomizer: N::RecordRandomizer = FromBytes::read_le(&mut reader)?;
        let record_view_key: N::RecordViewKey = FromBytes::read_le(&mut reader)?;

        Ok(Self::from(
            owner,
            value,
            payload,
            program_id,
            randomizer,
            record_view_key,
        )?)
    }
}

impl<N: Network> FromStr for Record<N> {
    type Err = RecordError;

    fn from_str(record: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(&record)?)
    }
}

impl<N: Network> fmt::Display for Record<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            serde_json::to_string(self).map_err::<fmt::Error, _>(serde::ser::Error::custom)?
        )
    }
}

impl<N: Network> Serialize for Record<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut record = serializer.serialize_struct("Record", 7)?;
                record.serialize_field("owner", &self.owner)?;
                record.serialize_field("value", &self.value)?;
                record.serialize_field("payload", &self.payload)?;
                record.serialize_field("program_id", &self.program_id)?;
                record.serialize_field("randomizer", &self.randomizer())?;
                record.serialize_field("record_view_key", &self.record_view_key)?;
                record.serialize_field("commitment", &self.commitment())?;
                record.end()
            }
            false => ToBytesSerializer::serialize(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Record<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                let record = serde_json::Value::deserialize(deserializer)?;
                let commitment: N::Commitment =
                    serde_json::from_value(record["commitment"].clone()).map_err(de::Error::custom)?;

                // Recover the record.
                let record = Self::from(
                    serde_json::from_value(record["owner"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(record["value"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(record["payload"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(record["program_id"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(record["randomizer"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(record["record_view_key"].clone()).map_err(de::Error::custom)?,
                )
                .map_err(de::Error::custom)?;

                // Ensure the commitment matches.
                match commitment == record.commitment() {
                    true => Ok(record),
                    false => Err(RecordError::InvalidCommitment(
                        commitment.to_string(),
                        record.commitment().to_string(),
                    ))
                    .map_err(de::Error::custom)?,
                }
            }
            false => FromBytesDeserializer::<Self>::deserialize(deserializer, "record", N::RECORD_SIZE_IN_BYTES),
        }
    }
}

impl<N: Network> Default for Record<N> {
    fn default() -> Self {
        Self::from(
            Default::default(),
            AleoAmount::ZERO,
            Default::default(),
            *N::noop_program_id(),
            Default::default(),
            Default::default(),
        )
        .expect("Failed to initialize Record::default()")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{testnet2::Testnet2, Address, PrivateKey};

    use rand::thread_rng;

    #[test]
    fn test_serde_json_noop() {
        let rng = &mut thread_rng();
        let address: Address<Testnet2> = PrivateKey::new(rng).into();

        // Noop record
        let expected_record = Record::new_noop(address, rng).unwrap();

        // Serialize
        let expected_string = expected_record.to_string();
        let candidate_string = serde_json::to_string(&expected_record).unwrap();
        assert_eq!(expected_string, candidate_string);

        // Deserialize
        assert_eq!(expected_record, Record::from_str(&candidate_string).unwrap());
        assert_eq!(expected_record, serde_json::from_str(&candidate_string).unwrap());
    }

    #[test]
    fn test_serde_json() {
        let rng = &mut thread_rng();
        let address: Address<Testnet2> = PrivateKey::new(rng).into();

        // Output record
        let mut payload = [0u8; Testnet2::RECORD_PAYLOAD_SIZE_IN_BYTES];
        rng.fill(&mut payload);
        let expected_record = Record::new(
            address,
            AleoAmount::from_i64(1234),
            Payload::from_bytes_le(&payload).unwrap(),
            *Testnet2::noop_program_id(),
            rng,
        )
        .unwrap();

        // Serialize
        let expected_string = expected_record.to_string();
        let candidate_string = serde_json::to_string(&expected_record).unwrap();
        assert_eq!(expected_string, candidate_string);

        // Deserialize
        assert_eq!(expected_record, Record::from_str(&candidate_string).unwrap());
        assert_eq!(expected_record, serde_json::from_str(&candidate_string).unwrap());
    }

    #[test]
    fn test_bincode_noop() {
        let rng = &mut thread_rng();
        let address: Address<Testnet2> = PrivateKey::new(rng).into();

        // Noop record
        let expected_record = Record::new_noop(address, rng).unwrap();

        // Serialize
        let expected_bytes = expected_record.to_bytes_le().unwrap();
        assert_eq!(&expected_bytes[..], &bincode::serialize(&expected_record).unwrap()[..]);

        // Deserialize
        assert_eq!(expected_record, Record::read_le(&expected_bytes[..]).unwrap());
        assert_eq!(expected_record, bincode::deserialize(&expected_bytes[..]).unwrap());
    }

    #[test]
    fn test_bincode() {
        let rng = &mut thread_rng();
        let address: Address<Testnet2> = PrivateKey::new(rng).into();

        // Output record
        let mut payload = [0u8; Testnet2::RECORD_PAYLOAD_SIZE_IN_BYTES];
        rng.fill(&mut payload);
        let expected_record = Record::new(
            address,
            AleoAmount::from_i64(1234),
            Payload::from_bytes_le(&payload).unwrap(),
            *Testnet2::noop_program_id(),
            rng,
        )
        .unwrap();

        // Serialize
        let expected_bytes = expected_record.to_bytes_le().unwrap();
        assert_eq!(&expected_bytes[..], &bincode::serialize(&expected_record).unwrap()[..]);

        // Deserialize
        assert_eq!(expected_record, Record::read_le(&expected_bytes[..]).unwrap());
        assert_eq!(expected_record, bincode::deserialize(&expected_bytes[..]).unwrap());
    }
}
