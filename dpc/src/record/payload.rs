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

use crate::{Network, RecordError};
use snarkvm_utilities::{FromBytes, FromBytesDeserializer, ToBytes, ToBytesSerializer};

use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
    marker::PhantomData,
    str::FromStr,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Payload<N: Network>(Vec<u8>, PhantomData<N>);

impl<N: Network> Payload<N> {
    pub fn from(bytes: &[u8]) -> Self {
        assert!(bytes.len() <= N::RECORD_PAYLOAD_SIZE_IN_BYTES);

        // Pad the bytes up to PAYLOAD_SIZE.
        let mut buffer = bytes.to_vec();
        buffer.resize(N::RECORD_PAYLOAD_SIZE_IN_BYTES, 0u8);

        Self(buffer, PhantomData)
    }

    pub fn is_empty(&self) -> bool {
        let mut payload = vec![0u8; N::RECORD_PAYLOAD_SIZE_IN_BYTES];
        payload.copy_from_slice(&self.0);
        payload == vec![0u8; N::RECORD_PAYLOAD_SIZE_IN_BYTES]
    }

    pub fn size() -> usize {
        N::RECORD_PAYLOAD_SIZE_IN_BYTES
    }

    pub fn as_any(&self) -> &dyn std::any::Any {
        self
    }
}

impl<N: Network> FromBytes for Payload<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let mut buffer = vec![0u8; N::RECORD_PAYLOAD_SIZE_IN_BYTES];
        reader.read_exact(&mut buffer)?;
        Ok(Self::from(&buffer))
    }
}

impl<N: Network> ToBytes for Payload<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.0.write_le(&mut writer)
    }
}

impl<N: Network> FromStr for Payload<N> {
    type Err = RecordError;

    fn from_str(payload_hex: &str) -> Result<Self, Self::Err> {
        Ok(Self::read_le(&hex::decode(payload_hex)?[..])?)
    }
}

impl<N: Network> fmt::Display for Payload<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let bytes = self.to_bytes_le().expect("Failed to convert payload to bytes");
        write!(f, "{}", hex::encode(bytes))
    }
}

impl<N: Network> Serialize for Payload<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => serializer.collect_str(self),
            false => ToBytesSerializer::serialize(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Payload<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => {
                FromBytesDeserializer::<Self>::deserialize(deserializer, "payload", N::RECORD_PAYLOAD_SIZE_IN_BYTES)
            }
        }
    }
}

impl<N: Network> Default for Payload<N> {
    fn default() -> Self {
        Self::from(&[])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testnet2::Testnet2;
    use snarkvm_utilities::Uniform;

    use rand::thread_rng;

    #[test]
    fn test_payload_from() {
        let rng = &mut thread_rng();

        // Create a random byte array, construct a payload from it, and check its byte array matches.
        for i in 0..Testnet2::RECORD_PAYLOAD_SIZE_IN_BYTES {
            let expected_payload = (0..i).map(|_| u8::rand(rng)).collect::<Vec<u8>>();
            let candidate_payload = Payload::<Testnet2>::from(&expected_payload).to_bytes_le().unwrap();
            assert_eq!(expected_payload, candidate_payload[0..i]);
            assert_eq!(vec![0u8; Testnet2::RECORD_PAYLOAD_SIZE_IN_BYTES - i], candidate_payload[i..]);
        }
    }

    #[test]
    fn test_serde_json() {
        let rng = &mut thread_rng();

        let expected_payload = Payload::<Testnet2>::from(
            &(0..Testnet2::RECORD_PAYLOAD_SIZE_IN_BYTES).map(|_| u8::rand(rng)).collect::<Vec<u8>>(),
        );

        // Serialize
        let expected_string = &expected_payload.to_string();
        let candidate_string = serde_json::to_string(&expected_payload).unwrap();
        assert_eq!(expected_string, serde_json::Value::from_str(&candidate_string).unwrap().as_str().unwrap());

        // Deserialize
        assert_eq!(expected_payload, Payload::from_str(expected_string).unwrap());
        assert_eq!(expected_payload, serde_json::from_str(&candidate_string).unwrap());
    }

    #[test]
    fn test_bincode() {
        let rng = &mut thread_rng();

        let expected_payload = Payload::<Testnet2>::from(
            &(0..Testnet2::RECORD_PAYLOAD_SIZE_IN_BYTES).map(|_| u8::rand(rng)).collect::<Vec<u8>>(),
        );

        // Serialize
        let expected_bytes = expected_payload.to_bytes_le().unwrap();
        assert_eq!(&expected_bytes[..], &bincode::serialize(&expected_payload).unwrap()[..]);

        // Deserialize
        assert_eq!(expected_payload, Payload::read_le(&expected_bytes[..]).unwrap());
        assert_eq!(expected_payload, bincode::deserialize(&expected_bytes[..]).unwrap());
    }
}
