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

impl<N: Network> Serialize for Execution<N> {
    /// Serializes the execution into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut execution = serializer.serialize_struct("Execution", 3)?;
                execution
                    .serialize_field("transitions", &self.transitions.values().collect::<Vec<&Transition<N>>>())?;
                execution.serialize_field("global_state_root", &self.global_state_root)?;
                if let Some(inclusion_proof) = &self.inclusion_proof {
                    execution.serialize_field("inclusion", inclusion_proof)?;
                }
                execution.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Execution<N> {
    /// Deserializes the execution from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                // Parse the execution from a string into a value.
                let mut execution = serde_json::Value::deserialize(deserializer)?;
                // Retrieve the transitions.
                let transitions: Vec<_> =
                    serde_json::from_value(execution["transitions"].take()).map_err(de::Error::custom)?;
                // Retrieve the global state root.
                let global_state_root =
                    serde_json::from_value(execution["global_state_root"].take()).map_err(de::Error::custom)?;
                // Retrieve the inclusion proof.
                let inclusion_proof =
                    serde_json::from_value(execution["inclusion"].take()).map_err(de::Error::custom)?;
                // Recover the execution.
                Self::from(transitions.into_iter(), global_state_root, inclusion_proof).map_err(de::Error::custom)
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "execution"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_serde_json() -> Result<()> {
        // Sample the execution.
        let expected = crate::process::test_helpers::sample_execution();

        // Serialize
        let expected_string = &expected.to_string();
        let candidate_string = serde_json::to_string(&expected)?;
        assert_eq!(expected, serde_json::from_str(&candidate_string)?);

        // Deserialize
        assert_eq!(expected, Execution::from_str(expected_string)?);
        assert_eq!(expected, serde_json::from_str(&candidate_string)?);

        Ok(())
    }

    #[test]
    fn test_bincode() -> Result<()> {
        // Sample the execution.
        let expected = crate::process::test_helpers::sample_execution();

        // Serialize
        let expected_bytes = expected.to_bytes_le()?;
        let expected_bytes_with_size_encoding = bincode::serialize(&expected)?;
        assert_eq!(&expected_bytes[..], &expected_bytes_with_size_encoding[8..]);

        // Deserialize
        assert_eq!(expected, Execution::read_le(&expected_bytes[..])?);
        assert_eq!(expected, bincode::deserialize(&expected_bytes_with_size_encoding[..])?);

        Ok(())
    }
}
