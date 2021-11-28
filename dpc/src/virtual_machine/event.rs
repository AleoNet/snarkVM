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

use crate::{Network, Operation};
use snarkvm_utilities::{FromBytes, FromBytesDeserializer, ToBytes, ToBytesSerializer};

use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
    str::FromStr,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Event<N: Network> {
    /// Emits publicly-visible arbitrary data.
    Custom(Vec<u8>),
    /// Emits the view key for an output record at the specified index in a transition.
    RecordViewKey(u8, N::RecordViewKey),
    /// Emits the operation performed in a transition.
    Operation(Operation<N>),
}

impl<N: Network> Event<N> {
    /// Returns the event ID.
    #[inline]
    fn id(&self) -> u8 {
        match self {
            Self::Custom(..) => 0,
            Self::RecordViewKey(..) => 1,
            Self::Operation(..) => 2,
        }
    }
}

impl<N: Network> FromBytes for Event<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let id: u8 = FromBytes::read_le(&mut reader)?;
        match id {
            0 => {
                let num_bytes: u16 = FromBytes::read_le(&mut reader)?;
                let mut buffer = vec![0u8; num_bytes as usize];
                reader.read_exact(&mut buffer)?;
                Ok(Self::Custom(buffer))
            }
            1 => {
                let index: u8 = FromBytes::read_le(&mut reader)?;
                let record_view_key: N::RecordViewKey = FromBytes::read_le(&mut reader)?;
                Ok(Self::RecordViewKey(index, record_view_key))
            }
            2 => Ok(Self::Operation(FromBytes::read_le(&mut reader)?)),
            _ => unreachable!("Invalid event ID during deserialization"),
        }
    }
}

impl<N: Network> ToBytes for Event<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.id().write_le(&mut writer)?;
        match self {
            Self::Custom(buffer) => {
                (buffer.len() as u16).write_le(&mut writer)?;
                buffer.write_le(&mut writer)
            }
            Self::RecordViewKey(index, record_view_key) => {
                index.write_le(&mut writer)?;
                record_view_key.write_le(&mut writer)
            }
            Self::Operation(operation) => operation.write_le(&mut writer),
        }
    }
}

impl<N: Network> FromStr for Event<N> {
    type Err = anyhow::Error;

    fn from_str(event: &str) -> Result<Self, Self::Err> {
        let event = serde_json::Value::from_str(event)?;
        let event_id: u8 = serde_json::from_value(event["id"].clone())?;

        match event_id {
            0 => {
                let bytes: String = serde_json::from_value(event["bytes"].clone())?;
                Ok(Self::Custom(hex::decode(bytes)?))
            }
            1 => {
                let index = serde_json::from_value(event["index"].clone())?;
                let record_view_key: String = serde_json::from_value(event["record_view_key"].clone())?;
                Ok(Self::RecordViewKey(index, serde_json::from_str(&record_view_key)?))
            }
            2 => {
                let operation = serde_json::from_value(event["operation"].clone())?;
                Ok(Self::Operation(operation))
            }
            _ => unreachable!(format!("Invalid event id {}", event_id)),
        }
    }
}

impl<N: Network> fmt::Display for Event<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let event = match self {
            Self::Custom(bytes) => {
                serde_json::json!({
                    "id": self.id(),
                    "bytes": hex::encode(bytes), // TODO (raychu86): Have serializer for bytes
                })
            }
            Self::RecordViewKey(index, record_view_key) => {
                serde_json::json!({
                    "id": self.id(),
                    "index": index,
                    "record_view_key": record_view_key.to_string(), // TODO (raychu86): Have serializer for record_view_key
                })
            }
            Self::Operation(operation) => {
                serde_json::json!({
                    "id": self.id(),
                    "operation": operation
                })
            }
        };

        write!(f, "{}", event)
    }
}

impl<N: Network> Serialize for Event<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => serializer.collect_str(self),
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Event<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "event"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testnet2::Testnet2;

    #[test]
    fn test_serde_json() {
        let expected_event = Event::<Testnet2>::Operation(Operation::Noop);

        // Serialize
        let expected_string = &expected_event.to_string();
        let candidate_string = serde_json::to_string(&expected_event).unwrap();
        assert_eq!(45, candidate_string.len(), "Update me if serialization has changed");
        assert_eq!(
            expected_string,
            serde_json::Value::from_str(&candidate_string)
                .unwrap()
                .as_str()
                .unwrap()
        );

        // Deserialize
        assert_eq!(expected_event, Event::from_str(&expected_string).unwrap());
        assert_eq!(expected_event, serde_json::from_str(&candidate_string).unwrap());
    }

    #[test]
    fn test_bincode() {
        let expected_event = Event::<Testnet2>::Operation(Operation::Noop);

        // Serialize
        let expected_bytes = expected_event.to_bytes_le().unwrap();
        let candidate_bytes = bincode::serialize(&expected_event).unwrap();
        assert_eq!(3, expected_bytes.len(), "Update me if serialization has changed");
        // TODO (howardwu): Serialization - Handle the inconsistency between ToBytes and Serialize (off by a length encoding).
        assert_eq!(&expected_bytes[..], &candidate_bytes[8..]);

        // Deserialize
        assert_eq!(expected_event, Event::read_le(&expected_bytes[..]).unwrap());
        assert_eq!(expected_event, bincode::deserialize(&candidate_bytes[..]).unwrap());
    }
}
