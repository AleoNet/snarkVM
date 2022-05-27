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

use crate::{Address, AleoAmount, Ciphertext, ComputeKey, DecryptionKey, Network, Payload, RecordError};
use snarkvm_algorithms::traits::{EncryptionScheme, PRF};
use snarkvm_curves::AffineCurve;
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{FromBits, FromBytes, FromBytesDeserializer, ToBits, ToBytes, ToBytesSerializer};

use core::hash::{Hash, Hasher};
use rand::{CryptoRng, Rng};
use serde::{de, ser::SerializeStruct, Deserialize, Deserializer, Serialize, Serializer};
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
    ops::Deref,
    str::FromStr,
};

#[derive(Clone, Debug)]
pub struct Record<N: Network> {
    owner: Address<N>,
    value: AleoAmount,
    payload: Option<Payload<N>>,
    record_view_key: N::RecordViewKey,
    ciphertext: N::RecordCiphertext,
}

impl<N: Network> Record<N> {
    /// Returns a new noop record.
    pub fn new_noop<R: Rng + CryptoRng>(owner: Address<N>, rng: &mut R) -> Result<Self, RecordError> {
        Self::new(owner, AleoAmount::ZERO, None, None, rng)
    }

    /// Returns a new record.
    pub fn new<R: Rng + CryptoRng>(
        owner: Address<N>,
        value: AleoAmount,
        payload: Option<Payload<N>>,
        program_id: Option<N::ProgramID>,
        rng: &mut R,
    ) -> Result<Self, RecordError> {
        // Generate the ciphertext parameters.
        let (_randomness, randomizer, record_view_key) =
            N::account_encryption_scheme().generate_asymmetric_key(&*owner, rng);
        Self::from(owner, value, payload, program_id, randomizer.into(), record_view_key.into())
    }

    /// Returns a record from the given inputs.
    pub fn from(
        owner: Address<N>,
        value: AleoAmount,
        payload: Option<Payload<N>>,
        program_id: Option<N::ProgramID>,
        randomizer: N::RecordRandomizer,
        record_view_key: N::RecordViewKey,
    ) -> Result<Self, RecordError> {
        // Encode the record contents into plaintext bytes.
        let mut plaintext = Vec::with_capacity(7);
        plaintext.push((*owner).to_x_coordinate()); // 32 bytes
        plaintext.extend_from_slice(
            <N::AccountEncryptionScheme as EncryptionScheme>::encode_message(&value.to_bytes_le()?)?.as_slice(),
        ); // 64 bits = 8 bytes
        plaintext.extend_from_slice(
            <N::AccountEncryptionScheme as EncryptionScheme>::encode_message(&match payload {
                Some(ref payload) => payload.to_bytes_le()?,
                None => Payload::<N>::default().to_bytes_le()?,
            })?
            .as_slice(),
        );

        // Determine if the record is a dummy.
        let is_dummy = value.is_zero() && payload.is_none() && program_id == None;

        // Encrypt the record bytes.
        let ciphertext = Ciphertext::<N>::from(
            randomizer,
            N::account_encryption_scheme().generate_symmetric_key_commitment(&record_view_key).into(),
            N::account_encryption_scheme().encrypt(&record_view_key, &plaintext),
            program_id,
            is_dummy,
        )?
        .into();

        Ok(Self { owner, value, payload, record_view_key, ciphertext })
    }

    /// Returns a record from the given decryption key and ciphertext.
    pub fn decrypt(decryption_key: &DecryptionKey<N>, ciphertext: &N::RecordCiphertext) -> Result<Self, RecordError> {
        // Decrypt the record ciphertext.
        let (plaintext, record_view_key) = (*ciphertext).to_plaintext(decryption_key)?;

        // Decode the plaintext bytes into the record contents.
        let owner = Address::<N>::read_le(&plaintext[0].to_bytes_le()?[..])?;
        let value = AleoAmount::read_le(&*N::AccountEncryptionScheme::decode_message(&[plaintext[1]])?)?;
        let payload = Some(Payload::read_le(&*N::AccountEncryptionScheme::decode_message(&plaintext[2..])?)?);

        // TODO (howardwu): TEMPORARY - Reintroduce this logic.
        // let payload = match plaintext.len() {
        //     2 => None,
        //     3 => Some(Payload::read_le(&*N::AccountEncryptionScheme::decode_message(&plaintext[2..])?)?),
        //     _ => return Err(anyhow!("Invalid plaintext size").into()),
        // };

        Ok(Self { owner, value, payload, record_view_key, ciphertext: ciphertext.clone() })
    }

    /// Returns `true` if the record is a dummy.
    pub fn is_dummy(&self) -> bool {
        self.value.is_zero() && self.payload.is_none() && self.program_id() == None
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
    pub fn payload(&self) -> &Option<Payload<N>> {
        &self.payload
    }

    /// Returns the program id of this record.
    pub fn program_id(&self) -> Option<N::ProgramID> {
        self.ciphertext.deref().program_id()
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
        // For our choice of scalar field and base field (i.e. a TE curve), the scalar field
        // is always smaller than base field, so the bytes always fit without wraparound.
        let seed = N::InnerScalarField::from_repr(FromBits::from_bits_le(&compute_key.sk_prf().to_bits_le()).unwrap())
            .unwrap();
        let input = self.commitment();
        let serial_number = N::SerialNumberPRF::prf(&seed, &input.into()).into();

        Ok(serial_number)
    }
}

impl<N: Network> PartialEq for Record<N> {
    fn eq(&self, other: &Self) -> bool {
        self.commitment() == other.commitment()
    }
}

impl<N: Network> Eq for Record<N> {}

impl<N: Network> Hash for Record<N> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.commitment().hash(state);
    }
}

impl<N: Network> ToBytes for Record<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.owner.write_le(&mut writer)?;
        self.value.write_le(&mut writer)?;

        match &self.payload {
            Some(payload) => {
                true.write_le(&mut writer)?;
                payload.write_le(&mut writer)?;
            }
            None => false.write_le(&mut writer)?,
        }

        match &self.program_id() {
            Some(program_id) => {
                true.write_le(&mut writer)?;
                program_id.write_le(&mut writer)?;
            }
            None => false.write_le(&mut writer)?,
        }

        self.randomizer().write_le(&mut writer)?;
        self.record_view_key.write_le(&mut writer)
    }
}

impl<N: Network> FromBytes for Record<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let owner: Address<N> = FromBytes::read_le(&mut reader)?;
        let value: AleoAmount = FromBytes::read_le(&mut reader)?;

        let payload_exists: bool = FromBytes::read_le(&mut reader)?;
        let payload: Option<Payload<N>> = match payload_exists {
            true => Some(FromBytes::read_le(&mut reader)?),
            false => None,
        };

        let program_id_exists: bool = FromBytes::read_le(&mut reader)?;
        let program_id: Option<N::ProgramID> = match program_id_exists {
            true => Some(FromBytes::read_le(&mut reader)?),
            false => None,
        };

        let randomizer: N::RecordRandomizer = FromBytes::read_le(&mut reader)?;
        let record_view_key: N::RecordViewKey = FromBytes::read_le(&mut reader)?;

        Ok(Self::from(owner, value, payload, program_id, randomizer, record_view_key)?)
    }
}

impl<N: Network> FromStr for Record<N> {
    type Err = RecordError;

    fn from_str(record: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(record)?)
    }
}

impl<N: Network> fmt::Display for Record<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", serde_json::to_string(self).map_err::<fmt::Error, _>(serde::ser::Error::custom)?)
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
                record.serialize_field("program_id", &self.program_id())?;
                record.serialize_field("randomizer", &self.randomizer())?;
                record.serialize_field("record_view_key", &self.record_view_key)?;
                record.serialize_field("commitment", &self.commitment())?;
                record.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
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
                    false => {
                        Err(RecordError::InvalidCommitment(commitment.to_string(), record.commitment().to_string()))
                            .map_err(de::Error::custom)?
                    }
                }
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "record"),
        }
    }
}

impl<N: Network> Default for Record<N> {
    fn default() -> Self {
        Self::from(Default::default(), AleoAmount::ZERO, None, None, Default::default(), Default::default())
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
            AleoAmount::from_gate(1234),
            Some(Payload::from_bytes_le(&payload).unwrap()),
            None,
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
        let candidate_bytes = bincode::serialize(&expected_record).unwrap();
        // TODO (howardwu): Serialization - Handle the inconsistency between ToBytes and Serialize (off by a length encoding).
        assert_eq!(&expected_bytes[..], &candidate_bytes[8..]);

        // Deserialize
        assert_eq!(expected_record, Record::read_le(&expected_bytes[..]).unwrap());
        assert_eq!(expected_record, bincode::deserialize(&candidate_bytes[..]).unwrap());
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
            AleoAmount::from_gate(1234),
            Some(Payload::from_bytes_le(&payload).unwrap()),
            None,
            rng,
        )
        .unwrap();

        // Serialize
        let expected_bytes = expected_record.to_bytes_le().unwrap();
        let candidate_bytes = bincode::serialize(&expected_record).unwrap();
        // TODO (howardwu): Serialization - Handle the inconsistency between ToBytes and Serialize (off by a length encoding).
        assert_eq!(&expected_bytes[..], &candidate_bytes[8..]);

        // Deserialize
        assert_eq!(expected_record, Record::read_le(&expected_bytes[..]).unwrap());
        assert_eq!(expected_record, bincode::deserialize(&candidate_bytes[..]).unwrap());
    }
}
