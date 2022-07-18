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

impl<N: Network> Serialize for Deployment<N> {
    /// Serializes the deployment into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut deployment = serializer.serialize_struct("Deployment", 3)?;
                deployment.serialize_field("edition", &self.edition)?;
                deployment.serialize_field("program", &self.program)?;
                deployment.serialize_field("verifying_keys", &self.verifying_keys)?;
                deployment.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Deployment<N> {
    /// Deserializes the deployment from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                // Parse the deployment from a string into a value.
                let deployment = serde_json::Value::deserialize(deserializer)?;

                // Recover the deployment.
                let deployment = Self::new(
                    // Retrieve the edition.
                    serde_json::from_value(deployment["edition"].clone()).map_err(de::Error::custom)?,
                    // Retrieve the program.
                    serde_json::from_value(deployment["program"].clone()).map_err(de::Error::custom)?,
                    // Retrieve the verifying keys.
                    serde_json::from_value(deployment["verifying_keys"].clone()).map_err(de::Error::custom)?,
                );

                Ok(deployment)
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "deployment"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_serde_json() -> Result<()> {
        // Sample the deployment.
        let expected = test_helpers::sample_deployment();

        // Serialize
        let expected_string = &expected.to_string();
        let candidate_string = serde_json::to_string(&expected)?;
        assert_eq!(expected, serde_json::from_str(&candidate_string)?);

        // Deserialize
        assert_eq!(expected, Deployment::from_str(expected_string)?);
        assert_eq!(expected, serde_json::from_str(&candidate_string)?);

        Ok(())
    }

    #[test]
    fn test_bincode() -> Result<()> {
        // Sample the deployment.
        let expected = test_helpers::sample_deployment();

        // Serialize
        let expected_bytes = expected.to_bytes_le()?;
        let expected_bytes_with_size_encoding = bincode::serialize(&expected)?;
        assert_eq!(&expected_bytes[..], &expected_bytes_with_size_encoding[8..]);

        // Deserialize
        assert_eq!(expected, Deployment::read_le(&expected_bytes[..])?);
        assert_eq!(expected, bincode::deserialize(&expected_bytes_with_size_encoding[..])?);

        Ok(())
    }
}
