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

impl<N: Network> Serialize for Request<N> {
    /// Serializes the request into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut transition = serializer.serialize_struct("Request", 9)?;
                transition.serialize_field("caller", &self.caller)?;
                transition.serialize_field("network", &self.network_id)?;
                transition.serialize_field("program", &self.program_id)?;
                transition.serialize_field("function", &self.function_name)?;
                transition.serialize_field("input_ids", &self.input_ids)?;
                transition.serialize_field("inputs", &self.inputs)?;
                transition.serialize_field("signature", &self.signature)?;
                transition.serialize_field("tvk", &self.tvk)?;
                transition.serialize_field("tsk", &self.tsk)?;
                transition.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Request<N> {
    /// Deserializes the request from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                // Parse the request from a string into a value.
                let request = serde_json::Value::deserialize(deserializer)?;
                // Recover the request.
                Ok(Self::from((
                    // Retrieve the caller.
                    serde_json::from_value(request["caller"].clone()).map_err(de::Error::custom)?,
                    // Retrieve the network ID.
                    serde_json::from_value(request["network"].clone()).map_err(de::Error::custom)?,
                    // Retrieve the program ID.
                    serde_json::from_value(request["program"].clone()).map_err(de::Error::custom)?,
                    // Retrieve the function name.
                    serde_json::from_value(request["function"].clone()).map_err(de::Error::custom)?,
                    // Retrieve the input IDs.
                    serde_json::from_value(request["input_ids"].clone()).map_err(de::Error::custom)?,
                    // Retrieve the inputs.
                    serde_json::from_value(request["inputs"].clone()).map_err(de::Error::custom)?,
                    // Retrieve the signature.
                    serde_json::from_value(request["signature"].clone()).map_err(de::Error::custom)?,
                    // Retrieve the `tvk`.
                    serde_json::from_value(request["tvk"].clone()).map_err(de::Error::custom)?,
                    // Retrieve the `tsk`.
                    serde_json::from_value(request["tsk"].clone()).map_err(de::Error::custom)?,
                )))
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "request"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_serde_json() -> Result<()> {
        for expected in test_helpers::sample_requests().into_iter() {
            // Serialize
            let expected_string = &expected.to_string();
            let candidate_string = serde_json::to_string(&expected)?;

            // Deserialize
            assert_eq!(expected, Request::from_str(expected_string)?);
            assert_eq!(expected, serde_json::from_str(&candidate_string)?);
        }
        Ok(())
    }

    #[test]
    fn test_bincode() {
        for expected in test_helpers::sample_requests().into_iter() {
            // Serialize
            let expected_bytes = expected.to_bytes_le().unwrap();
            let expected_bytes_with_size_encoding = bincode::serialize(&expected).unwrap();
            assert_eq!(&expected_bytes[..], &expected_bytes_with_size_encoding[8..]);

            // Deserialize
            assert_eq!(expected, Request::read_le(&expected_bytes[..]).unwrap());
            assert_eq!(expected, bincode::deserialize(&expected_bytes_with_size_encoding).unwrap());
        }
    }
}
