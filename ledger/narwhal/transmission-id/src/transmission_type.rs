// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// TODO (raychu86): Move this implementation.

use super::*;

/// The transmission type.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum TransmissionType {
    Ratification = 0,
    Transaction = 1,
    Solution = 2,
}

impl TransmissionType {
    /// Returns the transmission type name.
    pub fn type_name(&self) -> &str {
        match self {
            Self::Ratification => "ratification",
            Self::Transaction => "transaction",
            Self::Solution => "solution",
        }
    }

    /// Returns the transmission type for the given numeric identifier.
    pub fn from(type_id: u8) -> Result<Self> {
        match type_id {
            0 => Ok(Self::Ratification),
            1 => Ok(Self::Transaction),
            2 => Ok(Self::Solution),
            _ => bail!("Invalid transmission type"),
        }
    }

    /// Returns the unique numeric identifier for the transmission type.
    pub fn type_id(&self) -> u8 {
        *self as u8
    }
}

impl FromBytes for TransmissionType {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let type_id = u8::read_le(&mut reader)?;
        Self::from(type_id).map_err(|_| error("Failed to deserialize transmission type variant {type_id}"))
    }
}

impl ToBytes for TransmissionType {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.type_id().write_le(&mut writer)
    }
}

impl FromStr for TransmissionType {
    type Err = Error;

    /// Initializes the transmission type from a JSON-string.
    fn from_str(str: &str) -> Result<Self, Self::Err> {
        match str {
            "ratification" => Ok(Self::Ratification),
            "transaction" => Ok(Self::Transaction),
            "solution" => Ok(Self::Solution),
            _ => {
                bail!("Invalid transmission type")
            }
        }
    }
}

impl Debug for TransmissionType {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl Display for TransmissionType {
    /// Displays the transmission type as a JSON-string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.type_name())
    }
}

impl Serialize for TransmissionType {
    /// Serializes the transmission type into a string or as bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => serializer.collect_str(self),
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de> Deserialize<'de> for TransmissionType {
    /// Deserializes the transmission type from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "transmission type"),
        }
    }
}
