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

use super::*;

/// Enum of operations that can be performed to rollback a finalize operation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RollbackOperation<N: Network> {
    /// Rollback an mapping initialization, (`mapping ID`).
    InitializeMapping(Field<N>),
    /// Rollback a key-value insertion, (`mapping ID`, `key ID`).
    InsertKeyValue(Field<N>, Field<N>),
    /// Rollback a key-value update, (`mapping ID`, `index`, `key ID`, `previous value`).
    UpdateKeyValue(Field<N>, u64, Field<N>, Option<Value<N>>),
    /// Rollback a key-value removal, (`mapping ID`, `index`, `key`, `previous value`).
    RemoveKeyValue(Field<N>, u64, Plaintext<N>, Value<N>),
    /// Rollback a mapping removal, (`program ID`, `mapping name` `[(key, value)]`).
    RemoveMapping(ProgramID<N>, Identifier<N>, Vec<(Plaintext<N>, Value<N>)>),
}

impl<N: Network> RollbackOperation<N> {
    /// Returns the mapping ID of the rollback operation.
    pub fn mapping_id(&self) -> Result<Field<N>> {
        match self {
            RollbackOperation::InitializeMapping(mapping_id) => Ok(*mapping_id),
            RollbackOperation::InsertKeyValue(mapping_id, _) => Ok(*mapping_id),
            RollbackOperation::UpdateKeyValue(mapping_id, _, _, _) => Ok(*mapping_id),
            RollbackOperation::RemoveKeyValue(mapping_id, _, _, _) => Ok(*mapping_id),
            RollbackOperation::RemoveMapping(program_id, mapping_name, _) => {
                N::hash_bhp1024(&(program_id, mapping_name).to_bits_le())
            }
        }
    }
}

impl<N: Network> FromBytes for RollbackOperation<N> {
    /// Reads the rollback operation from buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the variant.
        let variant = u8::read_le(&mut reader)?;
        // Read the rollback operation.
        match variant {
            0 => {
                // Read the mapping ID.
                let mapping_id = Field::read_le(&mut reader)?;
                // Return the rollback operation.
                Ok(RollbackOperation::InitializeMapping(mapping_id))
            }
            1 => {
                // Read the mapping ID.
                let mapping_id = Field::read_le(&mut reader)?;
                // Read the key ID.
                let key_id = Field::read_le(&mut reader)?;
                // Return the rollback operation.
                Ok(RollbackOperation::InsertKeyValue(mapping_id, key_id))
            }
            2 => {
                // Read the mapping ID.
                let mapping_id = Field::read_le(&mut reader)?;
                // Read the index.
                let index = u64::read_le(&mut reader)?;
                // Read the key ID.
                let key_id = Field::read_le(&mut reader)?;
                // Read the previous value.
                let previous_value_variant = u8::read_le(&mut reader)?;
                let previous_value = match previous_value_variant {
                    0 => None,
                    1 => Some(Value::read_le(&mut reader)?),
                    _ => return Err(error("Invalid previous value variant")),
                };

                // Return the rollback operation.
                Ok(RollbackOperation::UpdateKeyValue(mapping_id, index, key_id, previous_value))
            }
            3 => {
                // Read the mapping ID.
                let mapping_id = Field::read_le(&mut reader)?;
                // Read the index.
                let index = u64::read_le(&mut reader)?;
                // Read the key.
                let key = Plaintext::read_le(&mut reader)?;
                // Read the previous value.
                let previous_value = Value::read_le(&mut reader)?;
                // Return the rollback operation.
                Ok(RollbackOperation::RemoveKeyValue(mapping_id, index, key, previous_value))
            }
            4 => {
                // Read the program ID.
                let program_id = ProgramID::read_le(&mut reader)?;
                // Read the mapping name.
                let mapping_name = Identifier::read_le(&mut reader)?;

                // Read the number of key-value pairs.
                let num_key_values = u32::read_le(&mut reader)?;
                // Read the key-value pairs.
                let mut key_values = Vec::with_capacity(num_key_values as usize);
                for _ in 0..num_key_values {
                    let key = Plaintext::read_le(&mut reader)?;
                    let value = Value::read_le(&mut reader)?;
                    key_values.push((key, value));
                }

                Ok(RollbackOperation::RemoveMapping(program_id, mapping_name, key_values))
            }
            5.. => Err(error(format!("Failed to decode rollback operation variant {variant}"))),
        }
    }
}

impl<N: Network> ToBytes for RollbackOperation<N> {
    /// Writes the rollback operation to buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            RollbackOperation::InitializeMapping(mapping_id) => {
                // Write the variant.
                0u8.write_le(&mut writer)?;
                // Write the mapping ID.
                mapping_id.write_le(&mut writer)?;
            }
            RollbackOperation::InsertKeyValue(mapping_id, key_id) => {
                // Write the variant.
                1u8.write_le(&mut writer)?;
                // Write the mapping ID.
                mapping_id.write_le(&mut writer)?;
                // Write the key ID.
                key_id.write_le(&mut writer)?;
            }
            RollbackOperation::UpdateKeyValue(mapping_id, index, key_id, previous_value) => {
                // Write the variant.
                2u8.write_le(&mut writer)?;
                // Write the mapping ID.
                mapping_id.write_le(&mut writer)?;
                // Write the index.
                index.write_le(&mut writer)?;
                // Write the key ID.
                key_id.write_le(&mut writer)?;

                // Write the previous value.
                match previous_value {
                    None => 0u8.write_le(&mut writer)?,
                    Some(ref value) => {
                        1u8.write_le(&mut writer)?;
                        value.write_le(&mut writer)?;
                    }
                }
            }
            RollbackOperation::RemoveKeyValue(mapping_id, index, key, previous_value) => {
                // Write the variant.
                3u8.write_le(&mut writer)?;
                // Write the mapping ID.
                mapping_id.write_le(&mut writer)?;
                // Write the index.
                index.write_le(&mut writer)?;
                // Write the key.
                key.write_le(&mut writer)?;
                // Write the previous value.
                previous_value.write_le(&mut writer)?;
            }
            RollbackOperation::RemoveMapping(program_id, mapping_name, key_values) => {
                // Write the variant.
                4u8.write_le(&mut writer)?;
                // Write the program ID.
                program_id.write_le(&mut writer)?;
                // Write the mapping name.
                mapping_name.write_le(&mut writer)?;

                // Write the number of key-value pairs.
                (key_values.len() as u32).write_le(&mut writer)?;
                // Write the key-value pairs.
                for (key, value) in key_values {
                    key.write_le(&mut writer)?;
                    value.write_le(&mut writer)?;
                }
            }
        }
        Ok(())
    }
}

impl<N: Network> Serialize for RollbackOperation<N> {
    /// Serializes the rollback operations to a JSON-string or buffer.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut operation = serializer.serialize_struct("RollbackOperation", 5)?;
                // Serialize the components.
                match self {
                    RollbackOperation::InitializeMapping(mapping_id) => {
                        operation.serialize_field("type", "initialize_mapping")?;
                        operation.serialize_field("mapping_id", mapping_id)?;
                    }
                    RollbackOperation::InsertKeyValue(mapping_id, key_id) => {
                        operation.serialize_field("type", "insert_key_value")?;
                        operation.serialize_field("mapping_id", mapping_id)?;
                        operation.serialize_field("key_id", key_id)?;
                    }
                    RollbackOperation::UpdateKeyValue(mapping_id, index, key_id, value_id) => {
                        operation.serialize_field("type", "update_key_value")?;
                        operation.serialize_field("mapping_id", mapping_id)?;
                        operation.serialize_field("index", index)?;
                        operation.serialize_field("key_id", key_id)?;
                        operation.serialize_field("value_id", value_id)?;
                    }
                    RollbackOperation::RemoveKeyValue(mapping_id, index, key_id, previous_value) => {
                        operation.serialize_field("type", "remove_key_value")?;
                        operation.serialize_field("mapping_id", mapping_id)?;
                        operation.serialize_field("index", index)?;
                        operation.serialize_field("key_id", key_id)?;
                        operation.serialize_field("previous_value", previous_value)?;
                    }
                    RollbackOperation::RemoveMapping(program_id, mapping_name, key_values) => {
                        operation.serialize_field("type", "remove_mapping")?;
                        operation.serialize_field("program_id", program_id)?;
                        operation.serialize_field("mapping_name", mapping_name)?;
                        operation.serialize_field("key_values", key_values)?;
                    }
                }
                operation.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for RollbackOperation<N> {
    /// Deserializes the rollback operations from a JSON-string or buffer.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                let mut operation = serde_json::Value::deserialize(deserializer)?;
                // Recover the operation.
                let rollback_operation = match operation.get("type").and_then(|t| t.as_str()) {
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
                        // Return the operation.
                        Self::InsertKeyValue(mapping_id, key_id)
                    }
                    Some("update_key_value") => {
                        // Deserialize the mapping ID.
                        let mapping_id = DeserializeExt::take_from_value::<D>(&mut operation, "mapping_id")?;
                        // Deserialize the index.
                        let index = DeserializeExt::take_from_value::<D>(&mut operation, "index")?;
                        // Deserialize the key ID.
                        let key_id = DeserializeExt::take_from_value::<D>(&mut operation, "key_id")?;
                        // Deserialize the previous_value.
                        let previous_value = DeserializeExt::take_from_value::<D>(&mut operation, "previous_value")?;
                        // Return the operation.
                        Self::UpdateKeyValue(mapping_id, index, key_id, previous_value)
                    }
                    Some("remove_key_value") => {
                        // Deserialize the mapping ID.
                        let mapping_id = DeserializeExt::take_from_value::<D>(&mut operation, "mapping_id")?;
                        // Deserialize the index.
                        let index = DeserializeExt::take_from_value::<D>(&mut operation, "index")?;
                        // Deserialize the key.
                        let key = DeserializeExt::take_from_value::<D>(&mut operation, "key")?;
                        // Deserialize the previous_value.
                        let previous_value = DeserializeExt::take_from_value::<D>(&mut operation, "previous_value")?;
                        // Return the operation.
                        Self::RemoveKeyValue(mapping_id, index, key, previous_value)
                    }
                    Some("remove_mapping") => {
                        // Deserialize the program ID.
                        let program_id = DeserializeExt::take_from_value::<D>(&mut operation, "program_id")?;
                        // Deserialize the mapping_name.
                        let mapping_name = DeserializeExt::take_from_value::<D>(&mut operation, "mapping_name")?;
                        // Deserialize the key values.
                        let key_values = DeserializeExt::take_from_value::<D>(&mut operation, "key_values")?;
                        // Return the operation.
                        Self::RemoveMapping(program_id, mapping_name, key_values)
                    }
                    _ => return Err(de::Error::custom("Invalid rollback operation type")),
                };
                // Return the operation.
                Ok(rollback_operation)
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "rollback operations"),
        }
    }
}
