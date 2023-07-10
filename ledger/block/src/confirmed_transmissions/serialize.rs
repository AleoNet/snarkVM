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

impl<N: Network> Serialize for ConfirmedTransmissions<N> {
    /// Serializes the confirmed transmissions to a JSON-string or buffer.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut confirmed_transmissions = serializer.serialize_struct("ConfirmedTransmissions", 3)?;
                confirmed_transmissions.serialize_field("transactions", &self.transactions)?;
                confirmed_transmissions.serialize_field("ratifications", &self.ratifications)?;

                if let Some(coinbase) = &self.coinbase {
                    confirmed_transmissions.serialize_field("coinbase", coinbase)?;
                }

                confirmed_transmissions.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for ConfirmedTransmissions<N> {
    /// Deserializes the confirmed transmissions from a JSON-string or buffer.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                let mut confirmed_transmissions = serde_json::Value::deserialize(deserializer)?;

                // Recover the confirmed transmissions.
                let confirmed_transmissions = Self::from(
                    DeserializeExt::take_from_value::<D>(&mut confirmed_transmissions, "transactions")?,
                    DeserializeExt::take_from_value::<D>(&mut confirmed_transmissions, "ratifications")?,
                    serde_json::from_value(
                        confirmed_transmissions.get_mut("coinbase").unwrap_or(&mut serde_json::Value::Null).take(),
                    )
                    .map_err(de::Error::custom)?,
                );

                Ok(confirmed_transmissions)
            }
            false => {
                FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "confirmed_transmissions")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_serde_json() -> Result<()> {
        let rng = &mut TestRng::default();

        for expected in [crate::confirmed_transmissions::test_helpers::sample_confirmed_transmissions(rng)].into_iter()
        {
            // Serialize
            let expected_string = &expected.to_string();
            let candidate_string = serde_json::to_string(&expected)?;

            // Deserialize
            assert_eq!(expected, ConfirmedTransmissions::from_str(expected_string)?);
            assert_eq!(expected, serde_json::from_str(&candidate_string)?);
        }
        Ok(())
    }

    #[test]
    fn test_bincode() -> Result<()> {
        let rng = &mut TestRng::default();

        for expected in [crate::confirmed_transmissions::test_helpers::sample_confirmed_transmissions(rng)].into_iter()
        {
            // Serialize
            let expected_bytes = expected.to_bytes_le()?;
            let expected_bytes_with_size_encoding = bincode::serialize(&expected)?;
            assert_eq!(&expected_bytes[..], &expected_bytes_with_size_encoding[8..]);

            // Deserialize
            assert_eq!(expected, ConfirmedTransmissions::read_le(&expected_bytes[..])?);
            assert_eq!(expected, bincode::deserialize(&expected_bytes_with_size_encoding[..])?);
        }
        Ok(())
    }
}
