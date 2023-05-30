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

use console::{network::prelude::*, types::Field};
use snarkvm_utilities::DeserializeExt;

/// Enum to represent the allowed set of Merkle tree operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FinalizeOperation<N: Network> {
    /// Appends a mapping to the program tree, as (`mapping ID`).
    InitializeMapping(Field<N>),
    /// Inserts a key-value leaf into the mapping tree,
    /// as (`mapping ID`, `key ID`, `value ID`).
    InsertKeyValue(Field<N>, Field<N>, Field<N>),
    /// Updates the key-value leaf at the given index in the mapping tree,
    /// as (`mapping ID`, `index`, `key ID`, `value ID`).
    UpdateKeyValue(Field<N>, u64, Field<N>, Field<N>),
    /// Removes the key-value leaf at the given index in the mapping tree,
    /// as (`mapping ID`, `index`).
    RemoveKeyValue(Field<N>, u64),
    /// Removes a mapping from the program tree, as (`mapping ID`).
    RemoveMapping(Field<N>),
}

impl<N: Network> FromBytes for FinalizeOperation<N> {
    /// Reads the finalize operation from buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the variant.
        let variant = u8::read_le(&mut reader)?;
        // Read the finalize operation.
        match variant {
            0 => {
                // Read the mapping ID.
                let mapping_id = Field::read_le(&mut reader)?;
                // Return the finalize operation.
                Ok(FinalizeOperation::InitializeMapping(mapping_id))
            }
            1 => {
                // Read the mapping ID.
                let mapping_id = Field::read_le(&mut reader)?;
                // Read the key ID.
                let key_id = Field::read_le(&mut reader)?;
                // Read the value ID.
                let value_id = Field::read_le(&mut reader)?;
                // Return the finalize operation.
                Ok(FinalizeOperation::InsertKeyValue(mapping_id, key_id, value_id))
            }
            2 => {
                // Read the mapping ID.
                let mapping_id = Field::read_le(&mut reader)?;
                // Read the index.
                let index = u64::read_le(&mut reader)?;
                // Read the key ID.
                let key_id = Field::read_le(&mut reader)?;
                // Read the value ID.
                let value_id = Field::read_le(&mut reader)?;
                // Return the finalize operation.
                Ok(FinalizeOperation::UpdateKeyValue(mapping_id, index, key_id, value_id))
            }
            3 => {
                // Read the mapping ID.
                let mapping_id = Field::read_le(&mut reader)?;
                // Read the index.
                let index = u64::read_le(&mut reader)?;
                // Return the finalize operation.
                Ok(FinalizeOperation::RemoveKeyValue(mapping_id, index))
            }
            4 => {
                // Read the mapping ID.
                let mapping_id = Field::read_le(&mut reader)?;
                // Return the finalize operation.
                Ok(FinalizeOperation::RemoveMapping(mapping_id))
            }
            5.. => Err(error(format!("Failed to decode finalize operation variant {variant}"))),
        }
    }
}

impl<N: Network> ToBytes for FinalizeOperation<N> {
    /// Writes the finalize operation to buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            FinalizeOperation::InitializeMapping(mapping_id) => {
                // Write the variant.
                0u8.write_le(&mut writer)?;
                // Write the mapping ID.
                mapping_id.write_le(&mut writer)?;
            }
            FinalizeOperation::InsertKeyValue(mapping_id, key_id, value_id) => {
                // Write the variant.
                1u8.write_le(&mut writer)?;
                // Write the mapping ID.
                mapping_id.write_le(&mut writer)?;
                // Write the key ID.
                key_id.write_le(&mut writer)?;
                // Write the value ID.
                value_id.write_le(&mut writer)?;
            }
            FinalizeOperation::UpdateKeyValue(mapping_id, index, key_id, value_id) => {
                // Write the variant.
                2u8.write_le(&mut writer)?;
                // Write the mapping ID.
                mapping_id.write_le(&mut writer)?;
                // Write the index.
                index.write_le(&mut writer)?;
                // Write the key ID.
                key_id.write_le(&mut writer)?;
                // Write the value ID.
                value_id.write_le(&mut writer)?;
            }
            FinalizeOperation::RemoveKeyValue(mapping_id, index) => {
                // Write the variant.
                3u8.write_le(&mut writer)?;
                // Write the mapping ID.
                mapping_id.write_le(&mut writer)?;
                // Write the index.
                index.write_le(&mut writer)?;
            }
            FinalizeOperation::RemoveMapping(mapping_id) => {
                // Write the variant.
                4u8.write_le(&mut writer)?;
                // Write the mapping ID.
                mapping_id.write_le(&mut writer)?;
            }
        }
        Ok(())
    }
}

impl<N: Network> Serialize for FinalizeOperation<N> {
    /// Serializes the finalize operations to a JSON-string or buffer.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut operation = serializer.serialize_struct("FinalizeOperation", 3)?;
                // Serialize the components.
                match self {
                    FinalizeOperation::InitializeMapping(mapping_id) => {
                        operation.serialize_field("type", "initialize_mapping")?;
                        operation.serialize_field("mapping_id", mapping_id)?;
                    }
                    FinalizeOperation::InsertKeyValue(mapping_id, key_id, value_id) => {
                        operation.serialize_field("type", "insert_key_value")?;
                        operation.serialize_field("mapping_id", mapping_id)?;
                        operation.serialize_field("key_id", key_id)?;
                        operation.serialize_field("value_id", value_id)?;
                    }
                    FinalizeOperation::UpdateKeyValue(mapping_id, index, key_id, value_id) => {
                        operation.serialize_field("type", "update_key_value")?;
                        operation.serialize_field("mapping_id", mapping_id)?;
                        operation.serialize_field("index", index)?;
                        operation.serialize_field("key_id", key_id)?;
                        operation.serialize_field("value_id", value_id)?;
                    }
                    FinalizeOperation::RemoveKeyValue(mapping_id, index) => {
                        operation.serialize_field("type", "remove_key_value")?;
                        operation.serialize_field("mapping_id", mapping_id)?;
                        operation.serialize_field("index", index)?;
                    }
                    FinalizeOperation::RemoveMapping(mapping_id) => {
                        operation.serialize_field("type", "remove_mapping")?;
                        operation.serialize_field("mapping_id", mapping_id)?;
                    }
                }
                operation.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for FinalizeOperation<N> {
    /// Deserializes the finalize operations from a JSON-string or buffer.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                let mut operation = serde_json::Value::deserialize(deserializer)?;
                // Recover the operation.
                let finalize_operation = match operation.get("type").and_then(|t| t.as_str()) {
                    Some("initialize_mapping") => {
                        // Deserialize the mapping ID.
                        let mapping_id = DeserializeExt::take_from_value::<D>(&mut operation, "mapping_id")?;
                        // Return the operation.
                        Self::InitializeMapping(mapping_id)
                    }
                    Some("insert_key_value") => {
                        // Deserialize the mapping ID.
                        let mapping_id = DeserializeExt::take_from_value::<D>(&mut operation, "mapping_id")?;
                        // Deserialize the key ID.
                        let key_id = DeserializeExt::take_from_value::<D>(&mut operation, "key_id")?;
                        // Deserialize the value ID.
                        let value_id = DeserializeExt::take_from_value::<D>(&mut operation, "value_id")?;
                        // Return the operation.
                        Self::InsertKeyValue(mapping_id, key_id, value_id)
                    }
                    Some("update_key_value") => {
                        // Deserialize the mapping ID.
                        let mapping_id = DeserializeExt::take_from_value::<D>(&mut operation, "mapping_id")?;
                        // Deserialize the index.
                        let index = DeserializeExt::take_from_value::<D>(&mut operation, "index")?;
                        // Deserialize the key ID.
                        let key_id = DeserializeExt::take_from_value::<D>(&mut operation, "key_id")?;
                        // Deserialize the value ID.
                        let value_id = DeserializeExt::take_from_value::<D>(&mut operation, "value_id")?;
                        // Return the operation.
                        Self::UpdateKeyValue(mapping_id, index, key_id, value_id)
                    }
                    Some("remove_key_value") => {
                        // Deserialize the mapping ID.
                        let mapping_id = DeserializeExt::take_from_value::<D>(&mut operation, "mapping_id")?;
                        // Deserialize the index.
                        let index = DeserializeExt::take_from_value::<D>(&mut operation, "index")?;
                        // Return the operation.
                        Self::RemoveKeyValue(mapping_id, index)
                    }
                    Some("remove_mapping") => {
                        // Deserialize the mapping ID.
                        let mapping_id = DeserializeExt::take_from_value::<D>(&mut operation, "mapping_id")?;
                        // Return the operation.
                        Self::RemoveMapping(mapping_id)
                    }
                    _ => return Err(de::Error::custom("Invalid finalize operation type")),
                };
                // Return the operation.
                Ok(finalize_operation)
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "finalize operations"),
        }
    }
}
