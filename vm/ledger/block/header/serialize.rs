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

impl<N: Network> Serialize for Header<N> {
    /// Serializes the header to a JSON-string or buffer.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut header = serializer.serialize_struct("BlockHeader", 8)?;
                header.serialize_field("previous_state_root", &self.previous_state_root)?;
                header.serialize_field("transactions_root", &self.transactions_root)?;
                header.serialize_field("network", &self.metadata.network)?;
                header.serialize_field("height", &self.metadata.height)?;
                header.serialize_field("round", &self.metadata.round)?;
                header.serialize_field("coinbase_target", &self.metadata.coinbase_target)?;
                header.serialize_field("proof_target", &self.metadata.proof_target)?;
                header.serialize_field("timestamp", &self.metadata.timestamp)?;
                header.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Header<N> {
    /// Deserializes the header from a JSON-string or buffer.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                let header = serde_json::Value::deserialize(deserializer)?;
                Ok(Self::from(
                    serde_json::from_value(header["previous_state_root"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(header["transactions_root"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(header["network"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(header["height"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(header["round"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(header["coinbase_target"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(header["proof_target"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(header["timestamp"].clone()).map_err(de::Error::custom)?,
                )
                .map_err(de::Error::custom)?)
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "block header"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_serde_json() -> Result<()> {
        for expected in [*crate::ledger::vm::test_helpers::sample_genesis_block().header()].into_iter() {
            // Serialize
            let expected_string = &expected.to_string();
            let candidate_string = serde_json::to_string(&expected)?;

            // Deserialize
            assert_eq!(expected, Header::from_str(expected_string)?);
            assert_eq!(expected, serde_json::from_str(&candidate_string)?);
        }
        Ok(())
    }

    #[test]
    fn test_bincode() -> Result<()> {
        for expected in [*crate::ledger::vm::test_helpers::sample_genesis_block().header()].into_iter() {
            // Serialize
            let expected_bytes = expected.to_bytes_le()?;
            let expected_bytes_with_size_encoding = bincode::serialize(&expected)?;
            assert_eq!(&expected_bytes[..], &expected_bytes_with_size_encoding[8..]);

            // Deserialize
            assert_eq!(expected, Header::read_le(&expected_bytes[..])?);
            assert_eq!(expected, bincode::deserialize(&expected_bytes_with_size_encoding[..])?);
        }
        Ok(())
    }
}
