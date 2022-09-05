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

use super::*;

impl<N: Network> Serialize for TransactionLeaf<N> {
    /// Serializes the leaf into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut leaf = serializer.serialize_struct("TransactionLeaf", 5)?;
                leaf.serialize_field("variant", &self.variant)?;
                leaf.serialize_field("index", &self.index)?;
                leaf.serialize_field("program_id", &self.program_id)?;
                leaf.serialize_field("function_name", &self.function_name)?;
                leaf.serialize_field("id", &self.id)?;
                leaf.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for TransactionLeaf<N> {
    /// Deserializes the leaf from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                // Parse the leaf from a string into a value.
                let leaf = serde_json::Value::deserialize(deserializer)?;
                // Recover the leaf.
                Ok(Self::new(
                    // Retrieve the variant.
                    serde_json::from_value(leaf["variant"].clone()).map_err(de::Error::custom)?,
                    // Retrieve the index.
                    serde_json::from_value(leaf["index"].clone()).map_err(de::Error::custom)?,
                    // Retrieve the program ID.
                    serde_json::from_value(leaf["program_id"].clone()).map_err(de::Error::custom)?,
                    // Retrieve the function name.
                    serde_json::from_value(leaf["function_name"].clone()).map_err(de::Error::custom)?,
                    // Retrieve the id.
                    serde_json::from_value(leaf["id"].clone()).map_err(de::Error::custom)?,
                ))
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "transaction leaf"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_serde_json() -> Result<()> {
        // Sample the leaf.
        let expected = test_helpers::sample_leaf();

        // Serialize
        let expected_string = &expected.to_string();
        let candidate_string = serde_json::to_string(&expected)?;
        assert_eq!(expected, serde_json::from_str(&candidate_string)?);

        // Deserialize
        assert_eq!(expected, TransactionLeaf::from_str(expected_string)?);
        assert_eq!(expected, serde_json::from_str(&candidate_string)?);

        Ok(())
    }

    #[test]
    fn test_bincode() -> Result<()> {
        // Sample the leaf.
        let expected = test_helpers::sample_leaf();

        // Serialize
        let expected_bytes = expected.to_bytes_le()?;
        let expected_bytes_with_size_encoding = bincode::serialize(&expected)?;
        assert_eq!(&expected_bytes[..], &expected_bytes_with_size_encoding[8..]);

        // Deserialize
        assert_eq!(expected, TransactionLeaf::read_le(&expected_bytes[..])?);
        assert_eq!(expected, bincode::deserialize(&expected_bytes_with_size_encoding[..])?);

        Ok(())
    }
}
