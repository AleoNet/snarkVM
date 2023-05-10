// Copyright (C) 2019-2023 Aleo Systems Inc.
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

use snarkvm_utilities::DeserializeExt;

impl<N: Network> Serialize for Metadata<N> {
    /// Serializes the metadata to a JSON-string or buffer.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut metadata = serializer.serialize_struct("Metadata", 8)?;
                metadata.serialize_field("network", &self.network)?;
                metadata.serialize_field("round", &self.round)?;
                metadata.serialize_field("height", &self.height)?;
                metadata.serialize_field("total_supply_in_microcredits", &self.total_supply_in_microcredits)?;
                metadata.serialize_field("cumulative_weight", &self.cumulative_weight)?;

                metadata.serialize_field("coinbase_target", &self.coinbase_target)?;
                metadata.serialize_field("proof_target", &self.proof_target)?;
                metadata.serialize_field("last_coinbase_target", &self.last_coinbase_target)?;
                metadata.serialize_field("last_coinbase_timestamp", &self.last_coinbase_timestamp)?;
                metadata.serialize_field("timestamp", &self.timestamp)?;
                metadata.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Metadata<N> {
    /// Deserializes the metadata from a JSON-string or buffer.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                let mut metadata = serde_json::Value::deserialize(deserializer)?;
                Ok(Self::new(
                    DeserializeExt::take_from_value::<D>(&mut metadata, "network")?,
                    DeserializeExt::take_from_value::<D>(&mut metadata, "round")?,
                    DeserializeExt::take_from_value::<D>(&mut metadata, "height")?,
                    DeserializeExt::take_from_value::<D>(&mut metadata, "total_supply_in_microcredits")?,
                    DeserializeExt::take_from_value::<D>(&mut metadata, "cumulative_weight")?,
                    DeserializeExt::take_from_value::<D>(&mut metadata, "coinbase_target")?,
                    DeserializeExt::take_from_value::<D>(&mut metadata, "proof_target")?,
                    DeserializeExt::take_from_value::<D>(&mut metadata, "last_coinbase_target")?,
                    DeserializeExt::take_from_value::<D>(&mut metadata, "last_coinbase_timestamp")?,
                    DeserializeExt::take_from_value::<D>(&mut metadata, "timestamp")?,
                )
                .map_err(de::Error::custom)?)
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "metadata"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_serde_json() -> Result<()> {
        let mut rng = TestRng::default();

        for expected in [*crate::vm::test_helpers::sample_genesis_block(&mut rng).metadata()].into_iter() {
            // Serialize
            let expected_string = &expected.to_string();
            let candidate_string = serde_json::to_string(&expected)?;

            // Deserialize
            assert_eq!(expected, Metadata::from_str(expected_string)?);
            assert_eq!(expected, serde_json::from_str(&candidate_string)?);
        }
        Ok(())
    }

    #[test]
    fn test_bincode() -> Result<()> {
        let mut rng = TestRng::default();

        for expected in [*crate::vm::test_helpers::sample_genesis_block(&mut rng).metadata()].into_iter() {
            // Serialize
            let expected_bytes = expected.to_bytes_le()?;
            let expected_bytes_with_size_encoding = bincode::serialize(&expected)?;
            assert_eq!(&expected_bytes[..], &expected_bytes_with_size_encoding[8..]);

            // Deserialize
            assert_eq!(expected, Metadata::read_le(&expected_bytes[..])?);
            assert_eq!(expected, bincode::deserialize(&expected_bytes_with_size_encoding[..])?);
        }
        Ok(())
    }
}
