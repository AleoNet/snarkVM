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

use crate::{Address, ComputeKey, Network, Payload, RecordError};
use snarkvm_algorithms::traits::{CommitmentScheme, PRF};
use snarkvm_utilities::{to_bytes_le, FromBytes, FromBytesDeserializer, ToBytes, ToBytesSerializer, UniformRand};

use rand::{CryptoRng, Rng};
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
    str::FromStr,
};

#[derive(Derivative)]
#[derivative(
    Default(bound = "N: Network"),
    Debug(bound = "N: Network"),
    Clone(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network")
)]
pub struct Record<N: Network> {
    owner: Address<N>,
    // TODO (raychu86) use AleoAmount which will guard the value range
    value: u64,
    payload: Payload<N>,
    program_id: N::ProgramID,
    serial_number_nonce: N::SerialNumber,
    commitment_randomness: N::CommitmentRandomness,
    commitment: N::Commitment,
}

impl<N: Network> Record<N> {
    /// Returns a new noop input record.
    pub fn new_noop_input<R: Rng + CryptoRng>(owner: Address<N>, rng: &mut R) -> Result<Self, RecordError> {
        Self::new_input(
            owner,
            0,
            Payload::<N>::default(),
            *N::noop_program_id(),
            UniformRand::rand(rng),
            UniformRand::rand(rng),
        )
    }

    /// Returns a new input record.
    pub fn new_input(
        owner: Address<N>,
        value: u64,
        payload: Payload<N>,
        program_id: N::ProgramID,
        serial_number_nonce: N::SerialNumber,
        commitment_randomness: N::CommitmentRandomness,
    ) -> Result<Self, RecordError> {
        Self::from(
            owner,
            value,
            payload,
            program_id,
            serial_number_nonce,
            commitment_randomness,
        )
    }

    /// Returns a new noop output record.
    pub fn new_noop_output<R: Rng + CryptoRng>(
        owner: Address<N>,
        serial_number_nonce: N::SerialNumber,
        rng: &mut R,
    ) -> Result<Self, RecordError> {
        Self::new_output(
            owner,
            0,
            Payload::<N>::default(),
            *N::noop_program_id(),
            serial_number_nonce,
            rng,
        )
    }

    /// Returns a new output record.
    pub fn new_output<R: Rng + CryptoRng>(
        owner: Address<N>,
        value: u64,
        payload: Payload<N>,
        program_id: N::ProgramID,
        serial_number_nonce: N::SerialNumber,
        rng: &mut R,
    ) -> Result<Self, RecordError> {
        Self::from(
            owner,
            value,
            payload,
            program_id,
            serial_number_nonce,
            UniformRand::rand(rng),
        )
    }

    pub fn from(
        owner: Address<N>,
        value: u64,
        payload: Payload<N>,
        program_id: N::ProgramID,
        serial_number_nonce: N::SerialNumber,
        commitment_randomness: N::CommitmentRandomness,
    ) -> Result<Self, RecordError> {
        // Determine if the record is a dummy.
        let is_dummy = value == 0 && payload.is_empty() && program_id == *N::noop_program_id();

        // Total = 32 + 1 + 8 + 128 + 48 + 32 = 249 bytes
        let commitment_input = to_bytes_le![
            owner,               // 256 bits = 32 bytes
            is_dummy,            // 1 bit = 1 byte
            value,               // 64 bits = 8 bytes
            payload,             // 1024 bits = 128 bytes
            program_id,          // 384 bits = 48 bytes
            serial_number_nonce  // 256 bits = 32 bytes
        ]?;

        // Compute the record commitment.
        let commitment = N::commitment_scheme()
            .commit(&commitment_input, &commitment_randomness)?
            .into();

        Ok(Self {
            program_id,
            owner,
            value,
            payload,
            serial_number_nonce,
            commitment_randomness,
            commitment,
        })
    }

    /// Returns `true` if the record is a dummy.
    pub fn is_dummy(&self) -> bool {
        self.value == 0 && self.payload.is_empty() && self.program_id == *N::noop_program_id()
    }

    /// Returns the record owner.
    pub fn owner(&self) -> Address<N> {
        self.owner
    }

    /// Returns the record value.
    pub fn value(&self) -> u64 {
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

    /// Returns the nonce used for the serial number.
    pub fn serial_number_nonce(&self) -> N::SerialNumber {
        self.serial_number_nonce
    }

    /// Returns the randomness used for the commitment.
    pub fn commitment_randomness(&self) -> N::CommitmentRandomness {
        self.commitment_randomness.clone()
    }

    /// Returns the commitment of this record.
    pub fn commitment(&self) -> N::Commitment {
        self.commitment
    }

    pub fn to_serial_number(&self, compute_key: &ComputeKey<N>) -> Result<N::SerialNumber, RecordError> {
        // Check that the compute key corresponds with the owner of the record.
        if self.owner != Address::<N>::from_compute_key(compute_key) {
            return Err(RecordError::IncorrectComputeKey);
        }

        // TODO (howardwu): CRITICAL - Review the translation from scalar to base field of `sk_prf`.
        // Compute the serial number.
        let seed = FromBytes::read_le(&compute_key.sk_prf().to_bytes_le()?[..])?;
        let input = &vec![self.serial_number_nonce.clone()];
        let serial_number = N::SerialNumberPRF::evaluate(&seed, input)?;

        Ok(serial_number)
    }
}

impl<N: Network> ToBytes for Record<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.owner.write_le(&mut writer)?;
        self.value.write_le(&mut writer)?;
        self.payload.write_le(&mut writer)?;
        self.program_id.write_le(&mut writer)?;
        self.serial_number_nonce.write_le(&mut writer)?;
        self.commitment_randomness.write_le(&mut writer)
    }
}

impl<N: Network> FromBytes for Record<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let owner: Address<N> = FromBytes::read_le(&mut reader)?;
        let value: u64 = FromBytes::read_le(&mut reader)?;
        let payload: Payload<N> = FromBytes::read_le(&mut reader)?;
        let program_id: N::ProgramID = FromBytes::read_le(&mut reader)?;
        let serial_number_nonce: N::SerialNumber = FromBytes::read_le(&mut reader)?;
        let commitment_randomness: N::CommitmentRandomness = FromBytes::read_le(&mut reader)?;

        Ok(Self::from(
            owner,
            value,
            payload,
            program_id,
            serial_number_nonce,
            commitment_randomness,
        )?)
    }
}

impl<N: Network> FromStr for Record<N> {
    type Err = RecordError;

    fn from_str(record: &str) -> Result<Self, Self::Err> {
        let record = serde_json::Value::from_str(record)?;
        let commitment: N::Commitment = serde_json::from_value(record["commitment"].clone())?;

        // Recover the record.
        let record = Self::from(
            serde_json::from_value(record["owner"].clone())?,
            serde_json::from_value(record["value"].clone())?,
            serde_json::from_value(record["payload"].clone())?,
            serde_json::from_value(record["program_id"].clone())?,
            serde_json::from_value(record["serial_number_nonce"].clone())?,
            serde_json::from_value(record["commitment_randomness"].clone())?,
        )?;

        // Ensure the commitment matches.
        match commitment == record.commitment() {
            true => Ok(record),
            false => Err(RecordError::InvalidCommitment(
                commitment.to_string(),
                record.commitment().to_string(),
            )),
        }
    }
}

impl<N: Network> fmt::Display for Record<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let record = serde_json::json!({
           "owner": self.owner,
           "value": self.value,
           "payload": self.payload,
           "program_id": self.program_id,
           "serial_number_nonce": self.serial_number_nonce,
           "commitment_randomness": self.commitment_randomness,
           "commitment": self.commitment
        });
        write!(f, "{}", record)
    }
}

impl<N: Network> Serialize for Record<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => serializer.collect_str(self),
            false => ToBytesSerializer::serialize(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Record<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => FromBytesDeserializer::<Self>::deserialize(deserializer, "record", N::RECORD_SIZE_IN_BYTES),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{testnet2::Testnet2, Address, PrivateKey};
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    #[test]
    fn test_serde_json_noop() {
        let rng = &mut thread_rng();
        let address: Address<Testnet2> = PrivateKey::new(rng).into();

        // Noop output record
        let expected_record = Record::new_noop_output(address, UniformRand::rand(rng), rng).unwrap();

        // Serialize
        let expected_string = &expected_record.to_string();
        let candidate_string = serde_json::to_string(&expected_record).unwrap();
        assert_eq!(
            expected_string,
            serde_json::Value::from_str(&candidate_string)
                .unwrap()
                .as_str()
                .unwrap()
        );

        // Deserialize
        assert_eq!(expected_record, Record::from_str(&expected_string).unwrap());
        assert_eq!(expected_record, serde_json::from_str(&candidate_string).unwrap());
    }

    #[test]
    fn test_serde_json() {
        let rng = &mut thread_rng();
        let address: Address<Testnet2> = PrivateKey::new(rng).into();

        // Output record
        let mut payload = [0u8; Testnet2::PAYLOAD_SIZE_IN_BYTES];
        rng.fill(&mut payload);
        let expected_record = Record::new_output(
            address,
            1234,
            Payload::from_bytes_le(&payload).unwrap(),
            *Testnet2::noop_program_id(),
            UniformRand::rand(rng),
            rng,
        )
        .unwrap();

        // Serialize
        let expected_string = &expected_record.to_string();
        let candidate_string = serde_json::to_string(&expected_record).unwrap();
        assert_eq!(
            expected_string,
            serde_json::Value::from_str(&candidate_string)
                .unwrap()
                .as_str()
                .unwrap()
        );

        // Deserialize
        assert_eq!(expected_record, Record::from_str(&expected_string).unwrap());
        assert_eq!(expected_record, serde_json::from_str(&candidate_string).unwrap());
    }

    #[test]
    fn test_bincode_noop() {
        let rng = &mut thread_rng();
        let address: Address<Testnet2> = PrivateKey::new(rng).into();

        // Noop output record
        let expected_record = Record::new_noop_output(address, UniformRand::rand(rng), rng).unwrap();

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
        let mut payload = [0u8; Testnet2::PAYLOAD_SIZE_IN_BYTES];
        rng.fill(&mut payload);
        let expected_record = Record::new_output(
            address,
            1234,
            Payload::from_bytes_le(&payload).unwrap(),
            *Testnet2::noop_program_id(),
            UniformRand::rand(rng),
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
